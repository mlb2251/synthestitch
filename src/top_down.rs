use clap::Parser;
use itertools::Itertools;
use serde::Serialize;
use std::{collections::{VecDeque, HashMap},sync::{Mutex, Arc}, thread};
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
    pub timeout: Option<u64>,

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
    #[clap(long, default_value = "5")]
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
}

#[derive(Clone, Debug, Default)]
struct LocalStats {
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
    crit: Mutex<CriticalMultithreadData<D>>,
    cfg: TopDownConfig,
    dsl: DSL<D>,
    model: M,
    prods: Vec<Prod>,
    track: Option<String>,
    tstart: Instant
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
    pub fn single_hole(tp: Type, env: VecDeque<Type>, typeset: TypeSet) -> PartialExpr {
        PartialExpr {expr: ExprSet::empty(Order::ParentFirst, false, false), ctx: typeset, holes: vec![Hole::new(tp,env,None)], prev_prod: None, ll: NotNan::new(0.).unwrap() }
    }
}

#[derive(Debug,Clone, PartialEq, Eq)]
pub struct Hole {
    pub tp: Type,
    pub env: VecDeque<Type>, // env[i] is $i
    pub parent: Option<Idx>, // parent of the hole - either the hole is the child of a lam or the right side of an app
}

impl Hole {
    fn new(tp: Type, env: VecDeque<Type>, parent: Option<Idx>) -> Hole {
        Hole {tp, env, parent}
    }
}



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
    pub fn apply_with_hole(self, expr: &mut PartialExpr) {
        self.apply_without_hole(expr);
        expr.holes.push(self.hole);
    }
    pub fn apply_without_hole(&self, expr: &mut PartialExpr) {
        expr.ctx.load_state(self.ctx_save_state);
        expr.prev_prod = self.prev_prod.clone();
        expr.ll = self.ll;
        expr.holes.truncate(self.hole_len);
        expr.expr.truncate(self.expr_len);
        if let Some(parent) = self.hole.parent {
            expr.expr.get_mut(parent).unexpand_right();
        }
    }
}

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
    pub fn apply(self, expr: &mut PartialExpr, hole: &Hole) {

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
                    new_hole_env.push_front(inner_arg_tp);
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

pub fn add_expansions(expr: &mut PartialExpr, expansions: &mut Vec<Expansion>, save_states: &mut Vec<SaveState>, prods: &[Prod], model: &impl ProbabilisticModel, lower_bound: NotNan<f32>) {
    // println!("b");
    let hole: Hole  = expr.holes.pop().unwrap();
    let hole_tp = hole.tp; 

    let mut expansions_buf = vec![];

    let ctx_save_state = expr.ctx.save_state();

    assert!(!hole_tp.is_arrow(&expr.ctx));
    // loop over all dsl entries and all variables in the env
    for prod in
        prods.iter().cloned()
        .chain(hole.env.iter().enumerate().map(|(i,tp)| Prod::Var(i as i32,*tp)))
    {
        expr.ctx.load_state(ctx_save_state);

        let (node,prod_tp) = match &prod {
            Prod::Prim(p, raw_tp_ref) => (Node::Prim(p.clone()), expr.ctx.instantiate(*raw_tp_ref)),
            Prod::Var(i, tp_ref) => (Node::Var(*i), tp_ref.clone()),
        };

        let unnormalized_ll = model.expansion_unnormalized_ll(&node, expr, &hole);

        if unnormalized_ll == f32::NEG_INFINITY {
            continue // skip directly
        }

        // unification check
        if !expr.ctx.unify(&hole_tp, &prod_tp.return_type(&expr.ctx)).is_ok() {
            continue;
        }
        

        expansions_buf.push(Expansion::new(prod, unnormalized_ll))
    }
    expr.ctx.load_state(ctx_save_state);

    
    // normalize
    let ll_total = expansions_buf.iter().map(|exp| exp.ll).reduce(logsumexp).unwrap_or(NotNan::new(f32::NEG_INFINITY).unwrap());
    for exp in expansions_buf.iter_mut() {
        exp.ll = expr.ll + (exp.ll - ll_total)
    }

    // LOWER BOUND: keep ones that are higher than the lower bound in probability
    // expansions_buf.retain(|exp| exp.ll > lower_bound); // cant easily fit a skip() in here but thats harmless so its ok
    let old_expansions_len = expansions.len();
    expansions.extend(expansions_buf.drain(..).filter(|exp| exp.ll > lower_bound));

    save_states.push(SaveState::new(expr, hole, expansions.len() - old_expansions_len));
}

pub fn top_down<D: Domain, M: ProbabilisticModel>(
    model: &M,
    dsl: &DSL<D>,
    all_tasks: &[Task<D>],
    cfg: &TopDownConfig,
) -> HashMap<TaskName, Vec<PartialExpr>> {

    println!("DSL:");
    for entry in dsl.productions.values() {
        println!("\t{} :: {}", entry.name, entry.tp);
    }

    let stats = Stats {
        local: Default::default(),
        num_solved_once: 0,
        num_never_solved: all_tasks.len(),
    };

    let tstart = Instant::now();

    let track = cfg.track.as_ref().map(|track| {
        // reparsing like this helps us catch errors in the track string and also
        // lets us guarantee the same syntax in terms of parens and spacing and `lam` vs `lambda` etc
        strip_lambdas(track)
    });

    let solutions: HashMap<TaskName, Vec<PartialExpr>> = all_tasks.iter().map(|task| (task.name.clone(), vec![])).collect();
    
    let mut typeset = TypeSet::empty();

    let unsolved_tasks: Vec<(Idx,Vec<Task<D>>)> = all_tasks.iter().map(|task| (task.tp.clone(), task.clone())).into_group_map()
        .into_iter().map(|(tp,tasks)| (typeset.add_tp(&tp),tasks)).collect();

    let mut prods: Vec<Prod> = dsl.productions.values().map(|entry| Prod::Prim(entry.name.clone(), typeset.add_tp(&entry.tp))).collect();
    // sort by arity as DC does to explore smaller things first (also sort  by name but thats just for determinism)
    prods.sort_by_key(|prod| {
        if let Prod::Prim(name, tp) = prod {
            (Type::new(*tp, 0).arity(&typeset),name.clone())
        } else { unreachable!() }
    });

    let work_item_generator = WorkItemGenerator {
        unsolved_tasks,
        cfg_min_ll: cfg.min_ll,
        cfg_step: cfg.step,
        curr: 0,
        curr_upper_bound: NotNan::new(0.).unwrap(),
        cfg_timeout: cfg.timeout.clone(),
        tstart,
    };

    let shared = Arc::new(Shared {
        crit: Mutex::new(CriticalMultithreadData { stats, work_item_generator, solutions }),
        cfg: cfg.clone(),
        dsl: dsl.clone(),
        model: model.clone(),
        prods,
        track,
        tstart,
    });

    if cfg.threads == 1 {
        // Single threaded
        search_worker(Arc::clone(&shared), &typeset);
    } else {
        // Multithreaded
        thread::scope(|scope| {
            let mut handles = vec![];
            for _ in 0..cfg.threads {
                // clone the Arcs to have copies for this thread
                let shared = Arc::clone(&shared);
                let typeset = typeset.clone();
                handles.push(scope.spawn(move || {
                    search_worker(shared, &typeset);
                }));
            }
        });
    }

    let shared = Arc::try_unwrap(shared).unwrap();

    if let Some(timeout) = shared.cfg.timeout {
        if shared.tstart.elapsed().as_secs() > timeout {
            println!("Timeout: stopped search at {} seconds", shared.tstart.elapsed().as_secs());
        }
    }

    let crit = shared.crit.lock().unwrap();
    println!("Final Stats: {:?}", crit.stats);
    crit.solutions.clone()
}

pub struct WorkItem<D: Domain> {
    tp: Idx,
    tasks: Vec<Task<D>>,
    upper_bound: NotNan<f32>,
    lower_bound: NotNan<f32>,
}

#[derive(Debug)]
pub struct WorkItemGenerator<D: Domain> {
    unsolved_tasks: Vec<(Idx,Vec<Task<D>>)>,
    cfg_min_ll: Option<f32>,
    cfg_step: f32,
    curr: usize, // index into unsolved_tasks
    curr_upper_bound: NotNan<f32>,
    cfg_timeout: Option<u64>,
    tstart: Instant
}

#[derive(Debug)]
pub struct CriticalMultithreadData<D: Domain> {
    stats: Stats,
    work_item_generator: WorkItemGenerator<D>,
    solutions: HashMap<TaskName, Vec<PartialExpr>>,
}

impl<D: Domain> Iterator for WorkItemGenerator<D> {
    type Item = WorkItem<D>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.unsolved_tasks.is_empty() {
            return None
        }
        if let Some(timeout) = self.cfg_timeout {
            if self.tstart.elapsed().as_secs() > timeout {
                return None
            }
        }

        if self.curr >= self.unsolved_tasks.len() {
            self.curr = 0;
            self.curr_upper_bound -= self.cfg_step;
            
            // global min ll cutoff check
            if let Some(min_ll) = self.cfg_min_ll {
                if *self.curr_upper_bound < min_ll {
                    return None
                }
            }
        }

        let (tp, tasks) = &self.unsolved_tasks[self.curr];
        let work_item = WorkItem {
            tp: *tp,
            tasks: tasks.clone(),
            upper_bound: self.curr_upper_bound,
            lower_bound: self.curr_upper_bound - self.cfg_step,
        };
        self.curr += 1;
        Some(work_item)
    }
}



fn search_worker<D: Domain, M: ProbabilisticModel>(shared: Arc<Shared<D,M>>, typeset: &TypeSet) {
    loop {
        let mut crit = shared.crit.lock().unwrap();
        let work_item = crit.work_item_generator.next();
        let elapsed = shared.tstart.elapsed().as_secs_f32();
        println!("{:?} @ {}s ({} processed/s)", crit.stats, elapsed, ((crit.stats.local.num_processed as f32) / elapsed) as i32 );
        drop(crit);
        match work_item {
            Some(work_item) => search_in_bounds(&work_item, &*shared, typeset),
            None => return
        }
    }
}


fn search_in_bounds<D: Domain, M: ProbabilisticModel>(work_item: &WorkItem<D>, shared: &Shared<D,M>, typeset: &TypeSet) {
    println!("Searching for <todo type> solutions in range {} <= ll <= {}:", work_item.lower_bound, work_item.upper_bound); // tp.tp(&original_typeset));
    for task in &work_item.tasks {
        println!("\t{}", task.name)
    }

    let mut typeset = typeset.clone();
    let tp =  typeset.instantiate(work_item.tp);

    // if we want to wrap this in some lambdas and return it, then the outermost lambda should be the first type in
    // the list of arg types. This will be the *largest* de bruijn index within the body of the program, therefore
    // we should reverse the 
    let mut env: VecDeque<Type> = if tp.is_arrow(&typeset) { tp.iter_args(&typeset).collect() } else { VecDeque::new() };
    env.make_contiguous().reverse();

    let mut save_states: Vec<SaveState> = vec![];
    let mut expansions: Vec<Expansion> = vec![];
    // let mut solutions: HashMap<TaskName, Vec<PartialExpr>> = Default::default();
    let mut expr = PartialExpr::single_hole(tp.return_type(&typeset), env.clone(), typeset);
    add_expansions(&mut expr, &mut expansions, &mut save_states, &shared.prods, &shared.model, work_item.lower_bound);

    let mut local_stats = LocalStats::default();

    loop {
        if let Some(timeout) = shared.cfg.timeout {
            if shared.tstart.elapsed().as_secs() > timeout {
                break
            }
        } 

        // check if totally done
        if save_states.is_empty() {
            break
        }

        // check if we need to pop our save state to pop a step upwards in DFS
        if save_states.last().unwrap().num_expansions == 0 {
            save_states.pop().unwrap().apply_with_hole(&mut expr);
            continue
        }

        // reset to the current save state
        save_states.last().unwrap().apply_without_hole(&mut expr);

        // apply the expansion
        expansions.pop().unwrap().apply(&mut expr, &save_states.last().unwrap().hole);
        save_states.last_mut().unwrap().num_expansions -= 1;

        assert!(expr.ll > work_item.lower_bound);

        local_stats.num_processed += 1;

        if let Some(track) = &shared.track {
            if !track.starts_with(expr.to_string().split("??").next().unwrap()) {
                if shared.cfg.verbose_worklist { println!("{}: {}","[pruned by track]".yellow(), expr ); }
                continue;
            }
        }

        if shared.cfg.verbose_worklist { println!("Processing {} | holes: {}", expr, expr.holes.len()); }

        if expr.holes.is_empty() {
            // newly completed program
            if expr.ll > work_item.upper_bound {
                continue; // too high probability - was enumerated on a previous pass of depth first search
            }
            local_stats.num_finished += 1;

            let solved_tasks = check_correctness(&shared, &work_item.tasks, &expr, &env, &mut local_stats);

            for task_name in solved_tasks {
                let mut crit = shared.crit.lock().unwrap();
                crit.stats.local.transfer(&mut local_stats);
                println!("{} {} [ll={}] @ {}s: {}", "Solved".green(), task_name, expr.ll, shared.tstart.elapsed().as_secs_f32(), expr);
                println!("Solved at: {:?}", crit.stats);
                let solutions = crit.solutions.get_mut(&task_name).unwrap();
                solutions.push(expr.clone());
                solutions.sort_by_key(|soln| -soln.ll);
                solutions.truncate(shared.cfg.num_solns);
                
                if solutions.len() == 1 {
                    crit.stats.num_never_solved -= 1;
                    crit.stats.num_solved_once += 1;
                } else if solutions.len() == shared.cfg.num_solns {
                    if let Some(idx) = crit.work_item_generator.unsolved_tasks.iter().position(|(tp, _)| tp == &work_item.tp) {
                        crit.work_item_generator.unsolved_tasks[idx].1.retain(|task| task.name != task_name);
                        if crit.work_item_generator.unsolved_tasks[idx].1.is_empty() {
                            crit.work_item_generator.unsolved_tasks.remove(idx);
                        }
                    }
                }

                drop(crit);
                if shared.cfg.one_soln {
                    return
                }
            }

        } else {
            // println!("{}: {} (ll={})", "expanding".yellow(), expr, expr.ll);
            add_expansions(&mut expr, &mut expansions, &mut save_states, &shared.prods, &shared.model, work_item.lower_bound);
        }
    }

    let mut crit = shared.crit.lock().unwrap();
    crit.stats.local.transfer(&mut local_stats);
    drop(crit);
}


#[inline(never)]
fn check_correctness<D: Domain, M: ProbabilisticModel>(shared: &Shared<D,M>, tasks: &[Task<D>], expanded: &PartialExpr, env: &VecDeque<Type>, local_stats: &mut LocalStats) -> Vec<TaskName> {
    let mut solved_tasks: Vec<TaskName> = vec![];

    // debug_assert!(expanded.expr.get(0).infer::<D>(&mut Context::empty(), &mut (env.clone())).is_ok());
    for task in tasks {
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



