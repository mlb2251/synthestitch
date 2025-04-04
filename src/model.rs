use crate::*;
use top_down::*;
use rustc_hash::FxHashSet;
use ordered_float::NotNan;



pub trait ProbabilisticModel: Clone + Send + Sync + std::fmt::Debug {
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
/// For us fix1() is the DC style fixpoint operator, and we set fix() to P=0 as it's really just necessary internally to implement fix1().
/// In our case, we dont force it to start with a fix1() but instead let that just be the usual distribution for the toplevel operator,
/// but then if we ever try to expand into a fix1() and we're not at the top level then we set P=0 immediately.
/// Furthermore since the first argument of fix is always $0 we modify probabilities to force that too.
#[derive(Clone, Debug)]
pub struct OrigamiModel<M: ProbabilisticModel> {
    model: M,
    fix1: Symbol,
    fix: Symbol
}

#[derive(Clone,Debug)]
pub struct SymmetryRuleModel<M: ProbabilisticModel> {
    model: M,
    rules: FxHashSet<(usize,Symbol,Symbol)>
}

impl<M: ProbabilisticModel> SymmetryRuleModel<M> {
    pub fn new(model: M, rules: &[(usize,&str,&str)]) -> SymmetryRuleModel<M> {
        let rules = rules.iter().map(|(a,b,c)| (*a,(*b).into(),(*c).into()) ).collect();
        SymmetryRuleModel { model, rules  }
    }

}

impl<M: ProbabilisticModel> OrigamiModel<M> {
    pub fn new(model: M, fix1: Symbol, fix: Symbol) -> Self {
        OrigamiModel { model, fix1, fix }
    }
}

impl<M: ProbabilisticModel> ProbabilisticModel for SymmetryRuleModel<M> {
    fn expansion_unnormalized_ll(&self, prod: &Node, expr: &PartialExpr, hole: &Hole) -> NotNan<f32> {
        // dreamcoders symmetry breaking rules
        if let Node::Prim(p) = prod {
            if let Some((Node::Prim(parent), arg_idx)) = parent_and_arg_idx(expr, hole) {
                if self.rules.contains(&(arg_idx,parent.clone(),p.clone())) {
                    return NotNan::new(f32::NEG_INFINITY).unwrap();
                }
            }
        }
        self.model.expansion_unnormalized_ll(prod, expr, hole)
    }
}

impl<M: ProbabilisticModel> ProbabilisticModel for OrigamiModel<M> {
    // #[inline(always)]
    fn expansion_unnormalized_ll(&self, prod: &Node, expr: &PartialExpr, hole: &Hole) -> NotNan<f32> {
        // if this is not the very first expansion, we forbid the fix1() operator
        if expr.expr.len() != 0 {
            if let Node::Prim(p) = prod  {
                if *p == self.fix1 {    
                    return NotNan::new(f32::NEG_INFINITY).unwrap();
                }
            }
        }

        // if this is the very first expansion, we require it to be the fix1() operator
        if expr.expr.len() == 0  {
            if let Node::Prim(p) = prod  {
                if *p != self.fix1 {    
                    return NotNan::new(f32::NEG_INFINITY).unwrap();
                }
            }
        }

        // if this is an expansion to the fix() operator, set it to 0
        if let Node::Prim(p) = prod  {
            if *p == self.fix {
                return NotNan::new(f32::NEG_INFINITY).unwrap();
            }
        }
        // if we previously expanded with fix1(), then force next expansion (ie first argument) to be $0
        if let Some(Node::Prim(p)) = &expr.prev_prod {
            if *p == self.fix1 {
                if let Node::Var(0,-1) = prod {
                    // doesnt really matter what we set this to as long as its not -inf, itll get normalized to ll=0 and P=1 since all other productions will be -inf
                    return NotNan::new(-1.).unwrap();
                } else {
                    return NotNan::new(f32::NEG_INFINITY).unwrap();
                }    
            }
        }
        // println!("{}", Expr::new(expr.expr.clone()).to_string_uncurried(expr.root.map(|u|u.into())));

        // we forbid the use of the very outermost argument if we used a fix1 at the top level
        if let Node::Var(i,-1) = prod {
            if *i+1 == hole.env.len() as i32 {
                if expr.expr.len() != 0 {
                    if let Node::App(f,_) = expr.expr[0] {
                        if let Node::App(f,_) = expr.expr[f] {
                            if expr.expr[f] == Node::Prim(self.fix1.clone()) {
                                return NotNan::new(f32::NEG_INFINITY).unwrap();
                            }
                        }
                    }
                }
            }
        }


        // default
        self.model.expansion_unnormalized_ll(prod, expr, hole)
    }
}


/// who is the parent of the hole and which child are we of it. Doesnt handle higher order stuff.
/// bc we didnt need that to replicate the dreamcoder symmetry rules
fn parent_and_arg_idx<'a>(expr: &'a PartialExpr, hole: &Hole) -> Option<(&'a Node, usize)> {
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
                return Some((&expr.expr[func], arg_idx));
            }
        }
    } else {
        return None // we dont handle Lams
    }
}

#[derive(Clone,Debug)]
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
    // #[inline(always)]
    fn expansion_unnormalized_ll(&self, prod: &Node, _expr: &PartialExpr, _hole: &Hole) -> NotNan<f32> {
        match prod {
            Node::Var(_,_) => self.var_ll,
            Node::Prim(_) => self.prim_ll,
            _ => unreachable!()
        }
    }
}
