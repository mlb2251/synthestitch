use clap::Parser;
use itertools::Itertools;
use serde::Serialize;
use std::{collections::{VecDeque, HashMap},sync::{Mutex, Arc}, thread, fmt::{Display, Formatter}};
use std::time::{Duration,Instant};
use colorful::Colorful;
use crate::*;


/// Top-down synthesis
#[derive(Parser, Debug, Serialize, Clone)]
#[clap(name = "Top-down synthesis")]
pub struct TopDownConfig {
    /// program to track
    #[clap(long)]
    pub track: Option<String>,

    /// never search below this ll (should be negative)
    #[clap(long)]
    pub min_ll: Option<f32>,

    /// timeout in seconds for the search
    #[clap(long)]
    pub timeout: Option<f32>,

    /// num threads to use
    #[clap(long, short='t', default_value = "1")]
    pub threads: usize,

    /// eval() timeout in milliseconds
    #[clap(long, default_value = "10")]
    pub eval_timeout: u64,

    /// how wide the ll range is during each step of search
    #[clap(long, default_value = "1.5")]
    pub step: f32,

    /// how many solutions to find per task
    #[clap(long, default_value = "1")]
    pub num_solns: usize,

    /// exit after very first solution to very first task that is solved
    #[clap(long)]
    pub one_soln: bool,

    /// print out every processed item
    #[clap(long)]
    pub verbose_worklist: bool,
       
    /// print out every evaluation result
    #[clap(long)]
    pub verbose_eval: bool,
    
}

#[derive(Clone, Debug)]
struct Stats {
    local: LocalStats,
    num_solved_once: usize,
    num_never_solved: usize,
    num_steals: usize,
}

#[derive(Clone, Debug, Default)]
pub struct LocalStats {
    num_processed: usize,
    num_finished: usize,
    num_eval_ok: usize,
    num_eval_err: usize,
}

impl LocalStats {
    fn transfer(&mut self, other: &mut Self) {
        self.num_processed += other.num_processed;
        other.num_processed = 0;
        self.num_finished += other.num_finished;
        other.num_finished = 0;
        self.num_eval_ok += other.num_eval_ok;
        other.num_eval_ok = 0;
        self.num_eval_err += other.num_eval_err;
        other.num_eval_err = 0;
    }
}

#[derive(Debug)]
struct Shared<D: Domain, M: ProbabilisticModel> {
    search_progress: Mutex<SearchProgress>,
    thread_states: Vec<Mutex<Option<ThreadState>>>,
    stats: Mutex<Stats>,
    cfg: TopDownConfig,
    dsl: DSL<D>,
    model: M,
    tasks: HashMap<TaskName,Task<D>>,
    prods: Vec<Prod>,
    track: Option<String>,
    tstart: Instant
}

#[derive(Debug,Clone)]
pub enum SearchStatus {
    NotStarted,
    Working(WorkItem),
    Done
}

#[derive(Debug,Clone)]
pub struct PartialExpr {
    pub expr: ExprSet,
    pub ctx: TypeSet, // typing context so far
    pub holes: Vec<Hole>, // holes so far
    pub prev_prod: Option<Node>, // previous production rule used, this is a Var | Prim or it's None if this is empty / the root
    pub ll: NotNan<f32>,
}

impl PartialExpr {
    pub fn single_hole(tp: Type, env: Vec<Type>, typeset: TypeSet) -> PartialExpr {
        PartialExpr {expr: ExprSet::empty(Order::ParentFirst, false, false), ctx: typeset, holes: vec![Hole::new(tp,env,None)], prev_prod: None, ll: NotNan::new(0.).unwrap() }
    }
}

#[derive(Debug,Clone, PartialEq, Eq)]
pub struct Hole {
    pub tp: Type,
    pub env: Vec<Type>, // env[i] is $i
    pub parent: Option<Idx>, // parent of the hole - either the hole is the child of a lam or the right side of an app
}

impl Hole {
    fn new(tp: Type, env: Vec<Type>, parent: Option<Idx>) -> Hole {
        Hole {tp, env, parent}
    }
}


#[derive(Debug,Clone)]
pub struct SaveState {
    hole: Hole, // hole that was expanded
    ctx_save_state: (usize,usize), // result of ctx.save_state() right before this expansion happened
    prev_prod: Option<Node>,
    ll: NotNan<f32>,
    hole_len: usize, // len of expr.holes (after removing the new `hole`)
    expr_len: usize,
    num_expansions: usize,
}



impl SaveState {
    pub fn new(expr: &PartialExpr, hole: Hole, num_expansions: usize) -> SaveState {
        SaveState { hole, ctx_save_state: expr.ctx.save_state(), prev_prod: expr.prev_prod.clone(), ll: expr.ll, hole_len: expr.holes.len(), expr_len: expr.expr.len(), num_expansions }
    }
}

impl ThreadState {
    pub fn pop_state(&mut self) {
        let state = self.save_states.pop().unwrap();
        self.expr.holes.push(state.hole);
    }
    pub fn reset_to_save_state(&mut self) {
        let expr = &mut self.expr;
        let state = self.save_states.last().unwrap();
        expr.ctx.load_state(state.ctx_save_state);
        expr.prev_prod = state.prev_prod.clone();
        expr.ll = state.ll;
        expr.holes.truncate(state.hole_len);
        expr.expr.truncate(state.expr_len);
        if let Some(parent) = state.hole.parent {
            expr.expr.get_mut(parent).unexpand_right();
        }
    }
}

#[derive(Clone,Debug)]
pub struct Expansion {
    prod: Prod,
    ll: NotNan<f32>,
}
#[derive(Clone,Debug)]
pub enum Prod {
    Prim(Symbol, Idx),
    Var(i32, Type)
}


impl Expansion {
    pub fn new(prod: Prod, ll: NotNan<f32>) -> Expansion {
        Expansion { prod, ll }
    }
    pub fn apply(self, state: &mut ThreadState) {
        let hole = &state.save_states.last().unwrap().hole;
        let expr = &mut state.expr;
        // perform unification - 
        // todo its weird and silly that we repeat this here
        // instantiate if this wasnt a variable
        let (prod,prod_tp) = match self.prod {
            Prod::Prim(p, raw_tp_ref) => (Node::Prim(p), expr.ctx.instantiate(raw_tp_ref)),
            Prod::Var(i, tp_ref) => (Node::Var(i), tp_ref),
        };
        
        expr.ctx.unify(&hole.tp, &prod_tp.return_type(&expr.ctx)).unwrap();

        expr.ll = self.ll;
        expr.prev_prod = Some(prod.clone());

        let mut to_expand: Option<Idx> = hole.parent.clone();

        // add a new hole for each arg, along with any apps and lams
        for arg_idx in (0..prod_tp.arity(&expr.ctx)).rev() {
            let arg_tp = prod_tp.iter_args(&expr.ctx).nth(arg_idx).unwrap();
            // make a new (app ?? ??)
            let mut idx: Idx = expr.expr.add(Node::App(HOLE, HOLE));
            // if this is the first arg then point the parent of the hole to this new app
            // otherwise point the previously generated app to this app
            if let Some(to_expand) = to_expand {
                expr.expr.get_mut(to_expand).expand(idx);
            }
            to_expand = Some(idx);

            // if this arg is higher order it may have arguments - we push those types onto our new env and push lambdas
            // into our expr
            let mut new_hole_env = hole.env.clone();
            if arg_tp.is_arrow(&expr.ctx) {
                for inner_arg_tp in arg_tp.iter_args(&expr.ctx) {
                    new_hole_env.insert(0, inner_arg_tp);
                    let lam_idx = expr.expr.add(Node::Lam(HOLE));
                    // adjust pointers so the previous app or lam we created points to this
                    expr.expr.get_mut(idx).expand_right(lam_idx);
                    idx = lam_idx;
                }
            }

            // the hole type is the return type of the arg (bc all lambdas were autofilled)
            let new_hole_tp = arg_tp.return_type(&expr.ctx).clone();
            expr.holes.push(Hole::new(new_hole_tp, new_hole_env, Some(idx)))
        }

        let idx = expr.expr.add(prod.clone());
        if let Some(to_expand) = to_expand {
            expr.expr.get_mut(to_expand).expand(idx);
        }

    }
}

pub fn add_expansions(state: &mut ThreadState, prods: &[Prod], model: &impl ProbabilisticModel, lower_bound: NotNan<f32>) {
    // println!("b");
    let hole: Hole  = state.expr.holes.pop().unwrap();
    let hole_tp = hole.tp; 

    let mut expansions_buf = vec![];

    let ctx_save_state = state.expr.ctx.save_state();

    assert!(!hole_tp.is_arrow(&state.expr.ctx));
    // loop over all dsl entries and all variables in the env
    for prod in
        prods.iter().cloned()
        .chain(hole.env.iter().enumerate().map(|(i,tp)| Prod::Var(i as i32,*tp)))
    {
        state.expr.ctx.load_state(ctx_save_state);

        let (node,prod_tp) = match &prod {
            Prod::Prim(p, raw_tp_ref) => (Node::Prim(p.clone()), state.expr.ctx.instantiate(*raw_tp_ref)),
            Prod::Var(i, tp_ref) => (Node::Var(*i), tp_ref.clone()),
        };

        let unnormalized_ll = model.expansion_unnormalized_ll(&node, &state.expr, &hole);

        if unnormalized_ll == f32::NEG_INFINITY {
            continue // skip directly
        }

        // unification check
        if !state.expr.ctx.unify(&hole_tp, &prod_tp.return_type(&state.expr.ctx)).is_ok() {
            continue;
        }
        

        expansions_buf.push(Expansion::new(prod, unnormalized_ll))
    }
    state.expr.ctx.load_state(ctx_save_state);

    
    // normalize
    let ll_total = expansions_buf.iter().map(|exp| exp.ll).reduce(logsumexp).unwrap_or(NotNan::new(f32::NEG_INFINITY).unwrap());
    for exp in expansions_buf.iter_mut() {
        exp.ll = state.expr.ll + (exp.ll - ll_total)
    }

    // LOWER BOUND: keep ones that are higher than the lower bound in probability
    // expansions_buf.retain(|exp| exp.ll > lower_bound); // cant easily fit a skip() in here but thats harmless so its ok
    let old_expansions_len = state.expansions.len();
    state.expansions.extend(expansions_buf.drain(..).filter(|exp| exp.ll > lower_bound));

    let num_expansions = state.expansions.len() - old_expansions_len;
    state.save_states.push(SaveState::new(&state.expr, hole, num_expansions));
}

pub fn top_down<D: Domain, M: ProbabilisticModel>(
    model: &M,
    dsl: &DSL<D>,
    all_tasks: &[Task<D>],
    cfg: &TopDownConfig,
) -> SearchProgress {

    println!("DSL:");
    for entry in dsl.productions.values() {
        println!("\t{} :: {}", entry.name, entry.tp);
    }

    let stats = Stats {
        local: Default::default(),
        num_solved_once: 0,
        num_never_solved: all_tasks.len(),
        num_steals: 0,
    };

    let tstart = Instant::now();

    let track = cfg.track.as_ref().map(|track| {
        // reparsing like this helps us catch errors in the track string and also
        // lets us guarantee the same syntax in terms of parens and spacing and `lam` vs `lambda` etc
        strip_lambdas(track)
    });

    // sort for determinism
    let mut all_tasks = all_tasks.to_vec();
    all_tasks.sort_by_key(|t|t.name.clone());

    let solutions: HashMap<TaskName, Vec<Solution>> = all_tasks.iter().map(|task| (task.name.clone(), vec![])).collect();
    
    let mut typeset = TypeSet::empty();

    let mut unsolved_tasks: Vec<(Idx,Vec<TaskName>)> = all_tasks.iter().map(|task| (task.tp.clone(), task.name.clone())).into_group_map()
        .into_iter().map(|(tp,tasks)| (typeset.add_tp(&tp),tasks)).collect();
    
    // sort for determinism, though it might already be
    unsolved_tasks.iter_mut().for_each(|(_,tasks)| tasks.sort());

    
    let tasks: HashMap<TaskName,Task<D>> = all_tasks.iter().map(|task| (task.name.clone(), task.clone())).collect();

    let mut prods: Vec<Prod> = dsl.productions.values().map(|entry| Prod::Prim(entry.name.clone(), typeset.add_tp(&entry.tp))).collect();
    // sort by arity as DC does to explore smaller things first (also sort  by name but thats just for determinism)
    prods.sort_by_key(|prod| {
        if let Prod::Prim(name, tp) = prod {
            (Type::new(*tp, 0).arity(&typeset),name.clone())
        } else { unreachable!() }
    });

    let search_progress = SearchProgress {
        status: SearchStatus::NotStarted,
        original_typeset: typeset.clone(),
        unsolved_tasks,
        solutions,
        curr: 0,
        curr_upper_bound: NotNan::new(0.).unwrap(),
        tstart,
        cfg: cfg.clone(),
    };

    let thread_states = (0..cfg.threads).map(|_| Mutex::new(None)).collect();

    let shared = Arc::new(Shared {
        search_progress: Mutex::new(search_progress),
        thread_states,
        stats: Mutex::new(stats),
        cfg: cfg.clone(),
        dsl: dsl.clone(),
        model: model.clone(),
        tasks,
        prods,
        track,
        tstart,
    });

    // lock scope
    { println!("{}", shared.search_progress.lock().unwrap().show(&*shared)); }

    if cfg.threads == 1 {
        // Single threaded
        search_worker(Arc::clone(&shared), 0);
    } else {
        // Multithreaded
        thread::scope(|scope| {
            let mut handles = vec![];
            for i in 0..cfg.threads {
                // clone the Arcs to have copies for this thread
                let shared = Arc::clone(&shared);
                handles.push(scope.spawn(move || {
                    search_worker(shared, i);
                }));
            }
        });
    }

    let shared = Arc::try_unwrap(shared).unwrap();

    if let Some(timeout) = shared.cfg.timeout {
        if shared.tstart.elapsed().as_secs_f32() > timeout {
            println!("{}: stopped search at {} seconds", "Timeout".red().bold(), shared.tstart.elapsed().as_secs_f32());
        }
    }

    { println!("{}", shared.search_progress.lock().unwrap().show(&shared)); }
    println!("Final: {:?}", shared.stats);
    println!("{}s", shared.tstart.elapsed().as_secs_f32());
    shared.search_progress.into_inner().unwrap()
}

#[derive(Debug, Clone)]
pub struct WorkItem {
    tp: Type,
    env: Vec<Type>,
    tasks: Vec<TaskName>,
    upper_bound: NotNan<f32>,
    lower_bound: NotNan<f32>,
}

#[derive(Debug)]
pub struct SearchProgress {
    pub status: SearchStatus,
    pub solutions: HashMap<TaskName, Vec<Solution>>,
    pub original_typeset: TypeSet,
    pub unsolved_tasks: Vec<(Idx,Vec<TaskName>)>,
    curr: usize, // index into unsolved_tasks
    curr_upper_bound: NotNan<f32>,
    tstart: Instant,
    cfg: TopDownConfig,
}

#[derive(Debug, Clone)]
pub struct Solution {
    pub task_name: TaskName,
    pub time_secs: f32,
    pub expr: PartialExpr,
    pub ll: NotNan<f32>,
    pub stats: LocalStats
}

impl Display for Solution {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[ll={:.3}] @ {:.3}s {}", self.ll, self.time_secs, self.expr)
    }
}


impl SearchProgress {
    fn show<D: Domain, M: ProbabilisticModel>(&self, shared: &Shared<D,M>) -> String {
        let mut s = String::new();
        s += "---------------------\n";
        s += &format!("Still enumerating for {} types:\n", self.unsolved_tasks.len());
        for (_, tasks) in self.unsolved_tasks.iter() {
            s += &format!("\t{} for [{} tasks]: {}\n", shared.tasks[tasks.first().unwrap()].tp, tasks.len(), tasks.iter().map(|t| t.to_string()).join(", "));
        }
        let mut tasks: Vec<TaskName> = self.solutions.keys().cloned().collect();
        tasks.sort();
        s += &format!("Solutions:");
        for name in &tasks {
            let solns = &self.solutions[name];
            if solns.is_empty() {
                s += &format!("\n\t{}: [{}]", name, "no solns".red());
            } else {
                let num_solns = format!("{} solns", solns.len()).green();
                s += &format!("\n\t{}: [{}] {}", name, num_solns, solns.first().unwrap());
            }
        }
        s += "\n---------------------";
        s
    }
}

impl Iterator for SearchProgress {
    type Item = (WorkItem,PartialExpr);
    fn next(&mut self) -> Option<Self::Item> {

        let unsolved_tasks = &mut self.unsolved_tasks;
        let all_solutions = &self.solutions;
        let num_solns = self.cfg.num_solns;

        unsolved_tasks.retain_mut(|(_tp,tasks)| {
            tasks.retain(|task| {
                let solns = all_solutions.get(task).unwrap();
                // retain if not enough solutions
                if solns.len() >= num_solns {
                    println!("{}: {}", "Done enumerating for task".green(), task);
                    false
                } else {
                    true
                }
            });
            // retain if there are tasks remaining
            if tasks.is_empty() {
                println!("{}: <type>", "Done enumerating for type".green());
                false
            } else {
                true
            }
        });

        if self.unsolved_tasks.is_empty() {
            return None
        }
        if let Some(timeout) = self.cfg.timeout {
            if self.tstart.elapsed().as_secs_f32() > timeout {
                return None
            }
        }

        if self.curr >= self.unsolved_tasks.len() {
            self.curr = 0;
            self.curr_upper_bound -= self.cfg.step;
            println!("{}: [{} < ll <= {}]", "Increasing depth".green(), self.curr_upper_bound - self.cfg.step, self.curr_upper_bound );
            
            // global min ll cutoff check
            if let Some(min_ll) = self.cfg.min_ll {
                if *self.curr_upper_bound < min_ll {
                    return None
                }
            }
        }

        let (tp, tasks) = &self.unsolved_tasks[self.curr];

        let mut typeset = self.original_typeset.clone();
        let tp = typeset.instantiate(*tp);

        // if we want to wrap this in some lambdas and return it, then the outermost lambda should be the first type in
        // the list of arg types. This will be the *largest* de bruijn index within the body of the program, therefore
        // we should reverse the 
        let mut env: Vec<Type> = if tp.is_arrow(&typeset) { tp.iter_args(&typeset).collect() } else { Vec::new() };
        // env.make_contiguous().reverse();
        env.reverse();

        let single_hole = PartialExpr::single_hole(tp.return_type(&typeset), env.clone(), typeset);

        let work_item = WorkItem {
            tp,
            env,
            tasks: tasks.clone(),
            upper_bound: self.curr_upper_bound,
            lower_bound: self.curr_upper_bound - self.cfg.step,
        };
        self.curr += 1;
        Some((work_item,single_hole))
    }
}



fn search_worker<D: Domain, M: ProbabilisticModel>(shared: Arc<Shared<D,M>>, thread_idx: usize) {

    loop {

        if let Some(timeout) = shared.cfg.timeout {
            if shared.tstart.elapsed().as_secs_f32() > timeout {
                return
            }
        }

        // if search is marked as done we can return, if it hasn't yet started we should keep waiting, otherwise proceed
        { // lock scope
            match shared.search_progress.lock().unwrap().status {
                SearchStatus::Done => return,
                SearchStatus::NotStarted => if thread_idx != 0 { continue },
                SearchStatus::Working(_) => {}
            }
        }

        // the point of this loop is to populate thread_states with something new, we should only enter here when it's set to None
        // lock scope
        { assert!(shared.thread_states[thread_idx].lock().unwrap().is_none()); }

        let mut new_state = None;
        let mut all_done = true;

        // try work stealing
        for state in shared.thread_states.iter() {
            // LOCK SAFETY: lock will drop at end of for-loop, and we aren't currently holding any locks and will not take
            // more locks during this block.
            // EFFICIENCY: We will block on any threads that are actively working, but since they release their lock once per
            // expansions and they do ~1M expansions per second, this is fine. Also, they won't mind that we took the lock
            // because this only happens when we are planning to save them some work and when we are being idle ourselves.
            if let Some(state) = state.lock().unwrap().as_mut() {
                all_done = false;

                // steal from the oldest save_state with 1+ expansions.
                let stolen_from = state.save_states.iter().position(|s| s.num_expansions > 0);
                // we can steal if there are 2+ expansion
                if let Some(stolen_from) = stolen_from {
                    // We will steal half of the expansions, or 1 if there is only 1 expansion
                    let num_to_take = std::cmp::max(1, state.save_states[stolen_from].num_expansions / 2);
                    let stolen_expansions = state.expansions.drain(0..num_to_take).collect();
                    state.save_states[stolen_from].num_expansions -= num_to_take;

                    new_state = Some(ThreadState {
                        save_states: state.save_states.clone(), // we don't care about the save states
                        expansions: stolen_expansions,
                        expr: state.expr.clone(),
                    });

                    // pop all the later save states until stolen_from is at the last position
                    while new_state.as_ref().unwrap().save_states.len() - 1 > stolen_from {
                        new_state.as_mut().unwrap().reset_to_save_state();
                        new_state.as_mut().unwrap().pop_state();
                    }
                    // set stolen_from to have just 1 expansion
                    new_state.as_mut().unwrap().save_states[stolen_from].num_expansions = num_to_take;

                    // println!("[Thread {:?}] {}", thread::current().id(), "Stole work".yellow());

                    shared.stats.lock().unwrap().num_steals += 1;

                    break
                }
            }
        }

        if all_done && thread_idx == 0 {

            // lock scope
            { println!("{}", shared.search_progress.lock().unwrap().show(&shared)); }
            { println!("Appx expansion rate: {} expansions/s", ((shared.stats.lock().unwrap().local.num_processed as f32) / shared.tstart.elapsed().as_secs_f32()) as i32); }


            // if no other threads are working, and we're the primary worker, we can generate new work
            // LOCK SAFETY: all_done means all other threads are just spinning in the search_worker loop waiting for
            // new work. They might take this mutex but only briefly to check .status, and never while holding any other locks.
            let mut search_progress = shared.search_progress.lock().unwrap();
            if let Some((work_item,single_hole)) = search_progress.next() {
                println!("[Thread {:?}] {} [{} < ll <= {}] {} @ {:.3}s", thread::current().id(), "Launching search".yellow(), work_item.lower_bound, work_item.upper_bound, shared.tasks[&work_item.tasks[0]].tp, shared.tstart.elapsed().as_secs_f32());
                let mut state = ThreadState {
                    save_states: vec![],
                    expansions: vec![],
                    expr: single_hole,
                };
                add_expansions(&mut state, &shared.prods, &shared.model, work_item.lower_bound);
                search_progress.status = SearchStatus::Working(work_item);
                // LOCK SAFETY: anyone holding our thread_state lock to steal from it will release it immediately when they find it has None,
                // so this will succeed quickly. Also, only we can make it not None so that couldn't have chanced from earlier.
                new_state = Some(state);
            } else {
                // there's no more work to be done - mark as Done so all other threads exit too
                search_progress.status = SearchStatus::Done;
                return
            }
        }
        
        // run search!
        if let Some(new_state) = new_state {
            // if new_state succeeded, we must have either just created work or stolen work

            // lock scope
            { *shared.thread_states[thread_idx].lock().unwrap() = Some(new_state); }


            let work_item = { // lock scope
                match &shared.search_progress.lock().unwrap().status {
                    SearchStatus::Working(work_item) => work_item.clone(),
                    _ => panic!("search_progress.status should be Working")
                }
            };

            // do the actual search
            let solutions = search_in_bounds(thread_idx, work_item, &*shared);

            // deal with solutions
            if !solutions.is_empty() {
                let mut search_progress = shared.search_progress.lock().unwrap();
                for soln in solutions {

                    let all_solutions = search_progress.solutions.get_mut(&soln.task_name).unwrap();

                    if all_solutions.len() == 1 {
                        // LOCK SAFETY: in no part of the code do we take the search progress lock while already holding the stats lock
                        let mut stats = shared.stats.lock().unwrap();
                        stats.num_never_solved -= 1;
                        stats.num_solved_once += 1;
                    }
            
                    all_solutions.push(soln.clone());
                    all_solutions.sort_by_key(|soln| -soln.ll); // stable sort is good here so that the first thing found stays first if it's high ll, so its timeout gets used for printing
                    all_solutions.truncate(shared.cfg.num_solns);
                }
                if shared.cfg.one_soln {
                    assert!(shared.cfg.threads == 1);
                    // shared.search_progress.lock().unwrap().status = SearchStatus::Done;
                    return
                }
            }

        }
    }
}

#[derive(Debug,Clone)]
pub struct ThreadState {
    pub save_states: Vec<SaveState>,
    pub expansions: Vec<Expansion>,
    pub expr: PartialExpr
}

fn search_in_bounds<D: Domain, M: ProbabilisticModel>(thread_idx: usize, work_item: WorkItem, shared: &Shared<D,M>) -> Vec<Solution> {

    let mut solutions = vec![];

    let mut local_stats = LocalStats::default();

    let mut time_check = 0;

    'outer:
    loop {
        
        // LOCK SAFETY: this lock() is inside of the scope of `loop{}` so that it is always dropped before
        // the next iteration or when exiting the loop. Therefore there will be a brief unlocked moment after each
        // iteration, during which time other threads can take the lock.
        let mut lock = shared.thread_states[thread_idx].lock().unwrap();
        let state = &mut lock.as_mut().unwrap();

        // only check time occasionally bc otherwise takes like 7% of runtime
        time_check += 1;
        if time_check == 1000 {
            time_check = 0;
            if let Some(timeout) = shared.cfg.timeout {
                if shared.tstart.elapsed().as_secs_f32() > timeout {
                    break
                }
            }
        }
        

        // occasionally transfer stats over. Note num_processed gets reset to 0 during a transfer
        if local_stats.num_processed >= 25_000 {
            shared.stats.lock().unwrap().local.transfer(&mut local_stats);
        }

        // check if totally done
        if state.expansions.is_empty() {
            break
        }

        // reset to the current save state
        state.reset_to_save_state();

        // check if we need to pop our save state to pop a step upwards in DFS
        if state.save_states.last().unwrap().num_expansions == 0 {
            // pop the last state.save_states and reinsert its hole into expr.holes
            state.pop_state();
            continue
        }

        // apply the expansion
        state.expansions.pop().unwrap().apply(state);
        state.save_states.last_mut().unwrap().num_expansions -= 1;

        assert!(state.expr.ll > work_item.lower_bound);

        local_stats.num_processed += 1;

        if let Some(track) = &shared.track {
            if !track.starts_with(state.expr.to_string().split("??").next().unwrap()) {
                if shared.cfg.verbose_worklist { println!("{}: {}","[pruned by track]".yellow(), state.expr ); }
                continue;
            }
        }

        if shared.cfg.verbose_worklist { println!("Processing {} | holes: {}", state.expr, state.expr.holes.len()); }

        if state.expr.holes.is_empty() {
            // newly completed program
            if state.expr.ll > work_item.upper_bound {
                continue; // too high probability - was enumerated on a previous pass of depth first search
            }
            local_stats.num_finished += 1;

            let solved_tasks = check_correctness(&shared, &work_item, &state.expr, &mut local_stats);

            for task_name in solved_tasks {

                // update the global stats and save a copy for this solution
                let solution_stats = { // lock scope
                    let mut global_stats = shared.stats.lock().unwrap();
                    global_stats.local.transfer(&mut local_stats);
                    global_stats.local.clone()
                };
                
                let soln = Solution { task_name: task_name.clone(), time_secs: shared.tstart.elapsed().as_secs_f32(), expr: state.expr.clone(), ll: state.expr.ll, stats: solution_stats };
                
                println!("[Thread {:?}] {} for {}: {}", thread::current().id(), "New Solution".green(), task_name, soln);
                println!("Soln Stats (may be up to 25,000 expansions in each other thread)  {:?}", soln.stats);

                solutions.push(soln);

                if shared.cfg.one_soln {
                    break 'outer
                }
            }

        } else {
            // println!("{}: {} (ll={})", "expanding".yellow(), expr, expr.ll);
            add_expansions(state, &shared.prods, &shared.model, work_item.lower_bound);
        }
    }

    // lock scope
    { shared.stats.lock().unwrap().local.transfer(&mut local_stats) };
    // lock scope
    { *shared.thread_states[thread_idx].lock().unwrap() = None; }
    solutions
}


#[inline(never)]
fn check_correctness<D: Domain, M: ProbabilisticModel>(shared: &Shared<D,M>, work_item: &WorkItem, expanded: &PartialExpr, local_stats: &mut LocalStats) -> Vec<TaskName> {
    let mut solved_tasks: Vec<TaskName> = vec![];

    // debug_assert!(expanded.expr.get(0).infer::<D>(&mut Context::empty(), &mut (work_item.env.clone())).is_ok());
    for task_name in work_item.tasks.iter() {
        let task = &shared.tasks[task_name];
        let mut solved = true;
        for io in task.ios.iter() {
            // probably excessively much cloning and such here lol
            let mut exec_env: Env<D> = io.inputs.clone().into();
            exec_env.reverse(); // for proper arg order

            // println!("about to exec");
            match expanded.expr.get(0).eval(&exec_env, &shared.dsl, Some(Duration::from_millis(shared.cfg.eval_timeout))) {
                Ok(res) => {
                    local_stats.num_eval_ok += 1;
                    if res == io.output {
                        if shared.cfg.verbose_eval { println!("{} {} {:?}", expanded, "=>".green(), res); }
                    } else {
                        if shared.cfg.verbose_eval { println!("{} {} {:?} != {:?}", expanded, "=>".yellow(), res, io.output); }
                        solved = false;
                        break
                    }
                },
                Err(err) => {
                    if shared.cfg.verbose_eval { println!("{} {} err: {}", "=>".red(), expanded, err); }
                    local_stats.num_eval_err += 1;
                    solved = false;
                    break
                }
            }
        }
        // solved_buf.push((unnormalized_ll, task.name.clone(), expanded.clone()));
        if solved {
            solved_tasks.push(task.name.clone());
        }
    }
   solved_tasks
}



