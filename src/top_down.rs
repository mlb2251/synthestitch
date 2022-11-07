use clap::Parser;
use itertools::Itertools;
use serde::Serialize;
use std::{collections::{VecDeque}, fmt::Display};
use ordered_float::NotNan;
use std::time::{Duration,Instant};
use lambdas::*;
use colorful::Colorful;
use crate::task::*;
use once_cell::sync::Lazy;

/// Top-down synthesis
#[derive(Parser, Debug, Serialize)]
#[clap(name = "Top-down synthesis")]
pub struct TopDownConfig {
    /// program to track
    #[clap(long)]
    pub t_track: Option<String>,

    /// min ll
    #[clap(long)]
    pub t_min_ll: Option<f32>,
    
}

#[derive(Clone, Debug, Default)]
struct Stats {
    num_eval_ok: usize,
    num_eval_err: usize,
    num_processed: usize,
    num_finished: usize,
}

#[derive(Debug,Clone)]
pub struct PartialExpr {
    expr: ExprSet,
    ctx: TypeSet, // typing context so far
    holes: Vec<Hole>, // holes so far
    prev_prod: Option<Node>, // previous production rule used, this is a Var | Prim or it's None if this is empty / the root
    ll: NotNan<f32>,
}

impl PartialExpr {
    pub fn single_hole(tp: TypeRef, env: VecDeque<TypeRef>, typeset: TypeSet) -> PartialExpr {
        PartialExpr {expr: ExprSet::empty(Order::ParentFirst, false), ctx: typeset, holes: vec![Hole::new(tp,env,None)], prev_prod: None, ll: NotNan::new(0.).unwrap() }
    }
}

impl Display for PartialExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.expr.get(0))
    }
}

#[derive(Debug,Clone, PartialEq, Eq)]
pub struct Hole {
    tp: TypeRef,
    env: VecDeque<TypeRef>, // env[i] is $i
    parent: Option<Idx>, // parent of the hole - either the hole is the child of a lam or the right side of an app
}

impl Hole {
    fn new(tp: TypeRef, env: VecDeque<TypeRef>, parent: Option<Idx>) -> Hole {
        Hole {tp, env, parent}
    }
}


pub trait ProbabilisticModel {
    fn expansion_unnormalized_ll(&self, prod: &Node, expr: &PartialExpr, hole: &Hole) -> NotNan<f32>;

    fn likelihood(_e: &Expr) -> NotNan<f32> {
        // todo implement this recursively making use of expansion_unnormalized_ll
        unimplemented!()
    }

}


/// This wraps a model to make it behave roughly like the DreamCoder enumerator, which when it detects a fixpoint operator
/// it give it 0% probability for using it lower in the program. Specifically what original DC does is
/// it forces the program to start with (lam (fix $0 ??)), then after the fact it may strip away that fix() operator if the function var
/// was never used in the body of the lambda.
/// For us fix_flip() is the DC style fixpoint operator, and we set fix() to P=0 as it's really just necessary internally to implement fix_flip().
/// In our case, we dont force it to start with a fix_flip() but instead let that just be the usual distribution for the toplevel operator,
/// but then if we ever try to expand into a fix_flip() and we're not at the top level then we set P=0 immediately.
/// Furthermore since the first argument of fix is always $0 we modify probabilities to force that too.
pub struct OrigamiModel<M: ProbabilisticModel> {
    model: M,
    fix_flip: Symbol,
    fix: Symbol
}

impl<M: ProbabilisticModel> OrigamiModel<M> {
    pub fn new(model: M, fix_flip: Symbol, fix: Symbol) -> Self {
        OrigamiModel { model, fix_flip, fix }
    }
}

static SYMMETRY_RULES: Lazy<Vec<(usize,Symbol,Symbol)>> = Lazy::new(|| vec![
    (0,"head","cons"), // arg_idx, parent, child
    (0,"head","[]"),
    (0,"tail","cons"),
    (0,"tail","[]"),
    (0,"+","0"),
    (1,"+","0"),
    (1,"-","0"),
    (0,"+","+"),
    (0,"*","*"),
    (0,"*","0"),
    (1,"*","0"),
    (0,"*","1"),
    (1,"*","1"),
    (0,"is_empty","cons"),
    (0,"is_empty","[]"),
].into_iter().map(|(x,s1,s2)| (x,s1.into(),s2.into())).collect());

impl<M: ProbabilisticModel> ProbabilisticModel for OrigamiModel<M> {
    fn expansion_unnormalized_ll(&self, prod: &Node, expr: &PartialExpr, hole: &Hole) -> NotNan<f32> {
        // if this is not the very first expansion, we forbid the fix_flip() operator
        if expr.expr.len() != 0 && *prod == Node::Prim(self.fix_flip.clone())  {
            return NotNan::new(f32::NEG_INFINITY).unwrap();
        }

        // if this is the very first expansion, we require it to be the fix_flip() operator
        if expr.expr.len() == 0 && *prod != Node::Prim(self.fix_flip.clone())  {
            return NotNan::new(f32::NEG_INFINITY).unwrap();
        }

        // if this is an expansion to the fix() operator, set it to 0
        if *prod == Node::Prim(self.fix.clone()) {
            return NotNan::new(f32::NEG_INFINITY).unwrap();
        }
        // if we previously expanded with fix_flip(), then force next expansion (ie first argument) to be $0
        if expr.prev_prod == Some(Node::Prim(self.fix_flip.clone())) {
            if let Node::Var(0) = prod {
                // doesnt really matter what we set this to as long as its not -inf, itll get normalized to ll=0 and P=1 since all other productions will be -inf
                return NotNan::new(-1.).unwrap();
            } else {
                return NotNan::new(f32::NEG_INFINITY).unwrap();
            }
        }
        // println!("{}", Expr::new(expr.expr.clone()).to_string_uncurried(expr.root.map(|u|u.into())));

        // we forbid the use of the very outermost argument if we used a fix_flip at the top level
        if let Node::Var(i) = prod {
            if *i+1 == hole.env.len() as i32 {
                if expr.expr.len() != 0 {
                    if let Node::App(f,_) = expr.expr[0] {
                        if let Node::App(f,_) = expr.expr[f] {
                            if expr.expr[f] == Node::Prim(self.fix_flip.clone()) {
                                return NotNan::new(f32::NEG_INFINITY).unwrap();
                            }
                        }
                    }
                }
            }
        }

        // dreamcoders symmetry breaking rules
        if let Node::Prim(p) = prod {
            if let Some((Node::Prim(parent), arg_idx)) = parent_and_arg_idx(expr, hole) {
                if SYMMETRY_RULES.contains(&(arg_idx,parent,p.clone())) {
                    return NotNan::new(f32::NEG_INFINITY).unwrap();
                }
            }
        }


        // default
        self.model.expansion_unnormalized_ll(prod, expr, hole)
    }
}


/// who is the parent of the hole and which child are we of it. Doesnt handle higher order stuff.
/// bc we didnt need that to replicate the dreamcoder symmetry rules
fn parent_and_arg_idx(expr: &PartialExpr, hole: &Hole) -> Option<(Node, usize)> {
    if hole.parent.is_none() {
        return None
    }
    if let Node::App(f,_) = expr.expr[hole.parent.unwrap()] {
        let mut arg_idx = 0;
        let mut func = f;
        loop {
            if let Node::App(f,_) = expr.expr[func] {
                arg_idx += 1;
                func = f;
            } else {
                return Some((expr.expr[func].clone(), arg_idx));
            }
        }
    } else {
        return None // we dont handle Lams
    }
}

pub struct UniformModel {
    var_ll: NotNan<f32>,
    prim_ll: NotNan<f32>,
}

impl UniformModel {
    pub fn new(var_ll: NotNan<f32>, prim_ll: NotNan<f32>) -> UniformModel {
        UniformModel { var_ll, prim_ll }
    }
}

impl ProbabilisticModel for UniformModel {
    fn expansion_unnormalized_ll(&self, prod: &Node, _expr: &PartialExpr, _hole: &Hole) -> NotNan<f32> {
        match prod {
            Node::Var(_) => self.var_ll,
            Node::Prim(_) => self.prim_ll,
            _ => unreachable!()
        }
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
    Prim(Symbol, RawTypeRef),
    Var(i32, TypeRef)
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
            Prod::Prim(p, raw_tp_ref) => (Node::Prim(p), raw_tp_ref.instantiate(&mut expr.ctx)),
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
            for inner_arg_tp in arg_tp.iter_args(&expr.ctx) {
                new_hole_env.push_front(inner_arg_tp);
                let lam_idx = expr.expr.add(Node::Lam(HOLE));
                // adjust pointers so the previous app or lam we created points to this
                expr.expr.get_mut(idx).expand_right(lam_idx);
                idx = lam_idx;
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

pub fn add_expansions<D: Domain, M: ProbabilisticModel>(expr: &mut PartialExpr, expansions: &mut Vec<Expansion>, save_states: &mut Vec<SaveState>, prods: &[Prod], model: &M, lower_bound: NotNan<f32>) {
    // println!("b");
    let hole: Hole  = expr.holes.pop().unwrap();
    let hole_tp = hole.tp; 

    let mut expansions_buf = vec![];

    let ctx_save_state = expr.ctx.save_state();
    // println!("hole type: {}", hole_tp);
    // println!("ctx: {:?}", expr.ctx);

    assert!(!hole_tp.is_arrow(&expr.ctx));
    // loop over all dsl entries and all variables in the env
    for prod in
        prods.iter().cloned()
        .chain(hole.env.iter().enumerate().map(|(i,tp)| Prod::Var(i as i32,*tp)))
    {
        expr.ctx.load_state(ctx_save_state);

        let (node,prod_tp) = match &prod {
            Prod::Prim(p, raw_tp_ref) => (Node::Prim(p.clone()), raw_tp_ref.instantiate(&mut expr.ctx)),
            Prod::Var(i, tp_ref) => (Node::Var(*i), tp_ref.clone()),
        };
        

        // println!("considering: {} :: {}", prod, prod_tp);
        // lightweight check for unification potential before doing the full clone and instantiation
        // if !expr.ctx.might_unify(&hole_tp, &prod_tp.return_type(&expr.ctx)) {
        //     continue
        // }

        // println!("passed might_unify()");

        // full unification check
        // println!("about to unify");
        if !expr.ctx.unify(&hole_tp, &prod_tp.return_type(&expr.ctx)).is_ok() {
            continue;
        }
        // println!("done unify");
        // println!("passed unify()");

        let unnormalized_ll = model.expansion_unnormalized_ll(&node, expr, &hole);

        if unnormalized_ll == f32::NEG_INFINITY {
            continue // skip directly
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

pub fn top_down_inplace<D: Domain, M: ProbabilisticModel>(
    model: M,
    all_tasks: &[Task<D>],
    cfg: &TopDownConfig,
) {

    println!("DSL:");
    for entry in D::dsl_entries() {
        println!("\t{} :: {}", entry.name, entry.tp);
    }

    let mut stats = Stats::default();

    let tstart = Instant::now();

    let budget_decr = NotNan::new(1.5).unwrap();
    let mut upper_bound = NotNan::new(0.).unwrap();
    let mut lower_bound = upper_bound - budget_decr;

    let mut original_typeset = TypeSet::empty();

    let task_tps: Vec<(RawTypeRef,Vec<Task<D>>)> = all_tasks.iter().map(|task| (task.tp.clone(), task.clone())).into_group_map()
        .into_iter().map(|(tp,tasks)| (original_typeset.add_tp(&tp),tasks)).collect();

    // let rawtyperef_of_tp: HashMap<Type,RawTypeRef> = task_tps
    //     .keys().cloned().chain(D::dsl_entries().map(|entry| entry.tp.clone()))
    //     .map(|tp| (tp.clone(),original_typeset.add_tp(&tp))).collect();

    let mut prods: Vec<Prod> = D::dsl_entries().map(|entry| Prod::Prim(entry.name.clone(), original_typeset.add_tp(&entry.tp))).collect();
    // sort by arity as DC does to explore smaller things first (also sort  by name but thats just for determinism)
    prods.sort_by_key(|prod| {
        if let Prod::Prim(name, tp) = prod {
            (tp.arity(&original_typeset),name.clone())
        } else { unreachable!() }
    });

    loop {

        if let Some(min_ll) =  cfg.t_min_ll {
            if *lower_bound <= min_ll {
                break
            }
        }



        for (tp, tasks) in task_tps.iter() {
            let elapsed = tstart.elapsed().as_secs_f32();
            println!("{:?} @ {}s ({} processed/s)", stats, elapsed, ((stats.num_processed as f32) / elapsed) as i32 );
            
            println!("Searching for {} solutions in range {lower_bound} <= ll <= {upper_bound}:", tp.tp(&original_typeset));
            for task in tasks {
                println!("\t{}", task.name)
            }


            let mut typeset = original_typeset.clone();
            let tp = tp.instantiate(&mut typeset);

            // if we want to wrap this in some lambdas and return it, then the outermost lambda should be the first type in
            // the list of arg types. This will be the *largest* de bruijn index within the body of the program, therefore
            // we should reverse the 
            let mut env: VecDeque<TypeRef> = tp.iter_args(&typeset).collect();
            env.make_contiguous().reverse();

            let mut save_states: Vec<SaveState> = vec![];
            let mut expansions: Vec<Expansion> = vec![];
            let mut solved_buf: Vec<(String, PartialExpr)> = vec![];
            let mut expr = PartialExpr::single_hole(tp.return_type(&typeset), env.clone(), typeset);
            add_expansions::<D,M>(&mut expr, &mut expansions, &mut save_states, &prods, &model, lower_bound);

            loop {
                // println!("a");
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

                assert!(expr.ll > lower_bound);

                stats.num_processed += 1;

                if let Some(track) = &cfg.t_track {
                    if !track.starts_with(expr.to_string().split("??").next().unwrap()) {
                        continue;
                    }
                }

                if expr.holes.is_empty() {
                    // newly completed program
                    if expr.ll > upper_bound {
                        continue; // too high probability - was enumerated on a previous pass of depth first search
                    }
                    stats.num_finished += 1;

                    let solved_tasks = check_correctness(tasks, &expr, &env, &mut stats, &mut solved_buf);

                    for task_name in solved_tasks {
                        println!("{} {} [ll={}] @ {}s: {}", "Solved".green(), task_name, expr.ll, tstart.elapsed().as_secs_f32(), expr);
                        println!("{:?}",stats);
                    }

                } else {
                    // println!("{}: {} (ll={})", "expanding".yellow(), expr, expr.ll);
                    add_expansions::<D,M>(&mut expr, &mut expansions, &mut save_states, &prods, &model, lower_bound);
                }

                // println!("holes: {:?}", item.expr.holes);
                // println!("ctx: {:?}", item.expr.ctx);

            }


        }

        lower_bound -= budget_decr;
        upper_bound -= budget_decr;
    }

    println!("{:?}", stats);


}

#[inline(never)]
fn check_correctness<D: Domain>(tasks: &Vec<Task<D>>, expanded: &PartialExpr, env: &VecDeque<TypeRef>, stats: &mut Stats, solved_buf: &mut Vec<(String, PartialExpr)>) -> Vec<String>{
    let mut solved_tasks: Vec<String> = vec![];

    // debug_assert!(expr.infer::<D>(Some(Id::from(expanded.root.unwrap())), &mut Context::empty(), &mut (env.clone())).is_ok());
    for task in tasks {
        let mut solved = true;
        for io in task.ios.iter() {
            // probably excessively much cloning and such here lol
            let mut exec_env: Vec<LazyVal<D>> = io.inputs.iter().map(|v| LazyVal::new_strict(v.clone())).collect();
            exec_env.reverse(); // for proper arg order

            // println!("about to exec");
            match expanded.expr.get(0).eval(&mut exec_env.clone(), Some(Duration::from_millis(10))) {
                Ok(res) => {
                    stats.num_eval_ok += 1;
                    if res == io.output {
                        // println!("{} {} {:?}", expanded, "=>".green(), res);
                    } else {
                        // println!("{} {} {:?}", expanded, "=>".yellow(), res);
                        solved = false;
                        break
                    }
                },
                Err(_) => {
                    // println!("{} {} err: {}", "=>".red(), expanded, err);
                    stats.num_eval_err += 1;
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




/// numerically stable streaming logsumexp (base 2)
/// equivalent to log(exp(x) + exp(y))
/// same as ADDING probabilities in normal probability space
#[inline(always)]
fn logsumexp(x: NotNan<f32>, y: NotNan<f32>) -> NotNan<f32> {
    if x.is_infinite() { return y }
    if y.is_infinite() { return x }
    let big = std::cmp::max(x,y);
    let smol = std::cmp::min(x,y);
    big + (1. + (smol - big).exp()).ln()
}
