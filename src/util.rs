use crate::*;

/// numerically stable streaming logsumexp (base 2)
/// equivalent to log(exp(x) + exp(y))
/// same as ADDING probabilities in normal probability space
#[inline(always)]
pub fn logsumexp(x: NotNan<f32>, y: NotNan<f32>) -> NotNan<f32> {
    if x.is_infinite() { return y }
    if y.is_infinite() { return x }
    let big = std::cmp::max(x,y);
    let smol = std::cmp::min(x,y);
    big + (1. + (smol - big).exp()).ln()
}

/// Takes a string, parses it into an Expr, unwraps any lambdas, and prints it back out.
/// This normalizes the string eg all `lambda` gets converted to `lam` etc, in addition to stripping
/// away lambdas
pub fn strip_lambdas(s: &str) -> String {
    let mut e = ExprSet::empty(Order::ChildFirst, false, false);
    let mut idx = e.parse_extend(s).unwrap();
    while let Node::Lam(b) = e.get(idx).node() {
        idx = *b;
    }
    e.get(idx).to_string()
}


impl std::fmt::Display for PartialExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.expr.get(0))
    }
}