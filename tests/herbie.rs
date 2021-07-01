use egg::*;
use indexmap::IndexMap;
use std::sync::atomic::{AtomicBool, Ordering};

use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{Pow, Signed, Zero};
use std::str::FromStr;
use std::time::Duration;

pub type Constant = num_rational::BigRational;
pub type RecExpr = egg::RecExpr<Math>;
pub type Pattern = egg::Pattern<Math>;
pub type EGraph = egg::EGraph<Math, ConstantFold>;
pub type Rewrite = egg::Rewrite<Math, ConstantFold>;
pub type Runner = egg::Runner<Math, ConstantFold, IterData>;
pub type TRunner = egg::Runner<Math, ConstantFold, ()>;
pub type Iteration = egg::Iteration<IterData>;

pub struct IterData {
    pub extracted: Vec<(Id, Extracted)>,
}

pub struct Extracted {
    pub best: RecExpr,
    pub cost: usize,
}

impl IterationData<Math, ConstantFold> for IterData {
    fn make(runner: &Runner) -> Self {
        let mut extractor = Extractor::new(&runner.egraph, AstSize);
        let extracted = runner
            .roots
            .iter()
            .map(|&root| {
                let (cost, best) = extractor.find_best(root);
                let ext = Extracted { cost, best };
                (root, ext)
            })
            .collect();
        Self { extracted }
    }
}

// operators from FPCore
define_language! {
    pub enum Math {

        // constant-folding operators

        "+" = Add([Id; 3]),
        "-" = Sub([Id; 3]),
        "*" = Mul([Id; 3]),
        "/" = Div([Id; 3]),
        "pow" = Pow([Id; 3]),
        "neg" = Neg([Id; 2]),
        "sqrt" = Sqrt([Id; 2]),
        "fabs" = Fabs([Id; 2]),
        "ceil" = Ceil([Id; 2]),
        "floor" = Floor([Id; 2]),
        "round" = Round([Id; 2]),

        Constant(Constant),
        Symbol(egg::Symbol),
        Other(egg::Symbol, Vec<Id>),
    }
}

pub struct ConstantFold {
    pub unsound: AtomicBool,
    pub constant_fold: bool,
    pub prune: bool,
}

impl Default for ConstantFold {
    fn default() -> Self {
        Self {
            constant_fold: true,
            prune: true,
            unsound: AtomicBool::from(false),
        }
    }
}

impl Analysis<Math> for ConstantFold {
    type Data = Option<(Constant, PatternAst<Math>)>;
    fn make(egraph: &EGraph, enode: &Math) -> Self::Data {
        if !egraph.analysis.constant_fold {
            return None;
        }

        let x = |id: &Id| egraph[*id].data.clone().map(|x| x.0);
        let is_zero = |id: &Id| {
            let data = egraph[*id].data.as_ref();
            match data {
                Some(data) => data.0.is_zero(),
                None => false,
            }
        };

        let mut missing_child = false;
        enode.for_each(|n| {
            if egraph[n].data == None {
                missing_child = true;
            }
        });
        if missing_child {
            return None;
        }

        Some((
            match enode {
                Math::Constant(c) => c.clone(),

                // real
                Math::Add([_p, a, b]) => x(a)? + x(b)?,
                Math::Sub([_p, a, b]) => x(a)? - x(b)?,
                Math::Mul([_p, a, b]) => x(a)? * x(b)?,
                Math::Div([_p, a, b]) => {
                    if x(b)?.is_zero() {
                        return None;
                    } else {
                        x(a)? / x(b)?
                    }
                }
                Math::Neg([_p, a]) => -x(a)?.clone(),
                Math::Pow([_p, a, b]) => {
                    if is_zero(b) && !is_zero(a) {
                        Ratio::new(BigInt::from(1), BigInt::from(1))
                    } else if is_zero(a) && !is_zero(b) {
                        Ratio::new(BigInt::from(0), BigInt::from(1))
                    } else if x(b)?.is_integer()
                        && !(x(a)?.is_zero() && (x(b)?.is_zero() || x(b)?.is_negative()))
                    {
                        Pow::pow(x(a)?, x(b)?.to_integer())
                    } else {
                        return None;
                    }
                }
                Math::Sqrt([_p, a]) => {
                    let a = x(a)?;
                    if *a.numer() > BigInt::from(0) && *a.denom() > BigInt::from(0) {
                        let s1 = a.numer().sqrt();
                        let s2 = a.denom().sqrt();
                        let is_perfect = &(&s1 * &s1) == a.numer() && &(&s2 * &s2) == a.denom();
                        if is_perfect {
                            Ratio::new(s1, s2)
                        } else {
                            return None;
                        }
                    } else {
                        return None;
                    }
                }
                Math::Fabs([_p, a]) => x(a)?.clone().abs(),
                Math::Floor([_p, a]) => x(a)?.floor(),
                Math::Ceil([_p, a]) => x(a)?.ceil(),
                Math::Round([_p, a]) => x(a)?.round(),

                _ => return None,
            },
            {
                let mut pattern: PatternAst<Math> = Default::default();
                enode.for_each(|child| {
                    if let Some(constant) = x(&child) {
                        pattern.add(ENodeOrVar::ENode(Math::Constant(constant)));
                    } else {
                        panic!("Child didn't have constant");
                    }
                });
                let mut counter = 0;
                let mut head = enode.clone();
                head.update_children(|_child| {
                    let res = Id::from(counter);
                    counter += 1;
                    res
                });
                pattern.add(ENodeOrVar::ENode(head));
                pattern
            },
        ))
    }

    fn merge(&self, to: &mut Self::Data, from: Self::Data) -> bool {
        match (&to, from) {
            (None, None) => false,
            (Some(_), None) => false, // no update needed
            (None, Some(c)) => {
                *to = Some(c);
                true
            }
            (Some(a), Some(ref b)) => {
                if a.0 != b.0 {
                    if !self.unsound.swap(true, Ordering::SeqCst) {
                        log::warn!("Bad merge detected: {} != {}", a.0, b.0);
                    }
                }
                false
            }
        }
    }

    fn modify(egraph: &mut EGraph, class_id: Id) {
        let class = &mut egraph[class_id];
        if let Some((c, node)) = class.data.clone() {
            let added = egraph.add(Math::Constant(c.clone()));
            let mut const_pattern: PatternAst<Math> = Default::default();
            const_pattern.add(ENodeOrVar::ENode(Math::Constant(c)));
            let (id, did_something) = egraph.union_with_reason(
                class_id,
                added,
                node,
                const_pattern,
                Default::default(),
                "metadata-eval".to_string(),
            );
            if false {
                egraph[id].nodes.retain(|n| n.is_leaf())
            }
        }
    }
}

pub fn mk_rules(tuples: &[(&str, &str, &str)]) -> Vec<Rewrite> {
    tuples
        .iter()
        .map(|(name, left, right)| {
            let left = Pattern::from_str(left).unwrap();
            let right = Pattern::from_str(right).unwrap();
            Rewrite::new(*name, left, right).unwrap()
        })
        .collect()
}

pub fn math_rules() -> Vec<Rewrite> {
    let mut rules: Vec<Rewrite> = Default::default();
    let mut add = |name, new_rules| {
        rules.extend(mk_rules(new_rules));
    };

    add("all-rules",
  &[
      ("not-true", "(not real (TRUE real))", "(FALSE real)"),
("not-false", "(not real (FALSE real))", "(TRUE real)"),
("not-not", "(not real (not real ?a))", "?a"),
("not-and", "(not real (and real ?a ?b))", "(or real (not real ?a) (not real ?b))"),
("not-or", "(not real (or real ?a ?b))", "(and real (not real ?a) (not real ?b))"),
("and-true-l", "(and real (TRUE real) ?a)", "?a"),
("and-true-r", "(and real ?a (TRUE real))", "?a"),
("and-false-l", "(and real (FALSE real) ?a)", "(FALSE real)"),
("and-false-r", "(and real ?a (FALSE real))", "(FALSE real)"),
("and-same", "(and real ?a ?a)", "?a"),
("or-true-l", "(or real (TRUE real) ?a)", "(TRUE real)"),
("or-true-r", "(or real ?a (TRUE real))", "(TRUE real)"),
("or-false-l", "(or real (FALSE real) ?a)", "?a"),
("or-false-r", "(or real ?a (FALSE real))", "?a"),
("or-same", "(or real ?a ?a)", "?a"),
("erfc-erf_binary64", "(erf f64 ?x)", "(- f64 1 (erfc f64 ?x))"),
("erf-erfc_binary64", "(erfc f64 ?x)", "(- f64 1 (erf f64 ?x))"),
("erf-odd_binary64", "(erf f64 (neg f64 ?x))", "(neg f64 (erf f64 ?x))"),
("if-if-and-not_binary64", "(if real ?a (if real ?b ?y ?x) ?y)", "(if real (and real ?a (not real ?b)) ?x ?y)"),
("if-if-and_binary64", "(if real ?a (if real ?b ?x ?y) ?y)", "(if real (and real ?a ?b) ?x ?y)"),
("if-if-or-not_binary64", "(if real ?a ?x (if real ?b ?y ?x))", "(if real (or real ?a (not real ?b)) ?x ?y)"),
("if-if-or_binary64", "(if real ?a ?x (if real ?b ?x ?y))", "(if real (or real ?a ?b) ?x ?y)"),
("if-not_binary64", "(if real (not real ?a) ?x ?y)", "(if real ?a ?y ?x)"),
("if-same_binary64", "(if real ?a ?x ?x)", "?x"),
("if-false_binary64", "(if real (FALSE real) ?x ?y)", "?y"),
("if-true_binary64", "(if real (TRUE real) ?x ?y)", "?x"),
("not-gte_binary64", "(not real (>= f64 ?x ?y))", "(< f64 ?x ?y)"),
("not-lte_binary64", "(not real (<= f64 ?x ?y))", "(> f64 ?x ?y)"),
("not-gt_binary64", "(not real (> f64 ?x ?y))", "(<= f64 ?x ?y)"),
("not-lt_binary64", "(not real (< f64 ?x ?y))", "(>= f64 ?x ?y)"),
("gte-same_binary64", "(>= f64 ?x ?x)", "(TRUE real)"),
("lte-same_binary64", "(<= f64 ?x ?x)", "(TRUE real)"),
("gt-same_binary64", "(> f64 ?x ?x)", "(FALSE real)"),
("lt-same_binary64", "(< f64 ?x ?x)", "(FALSE real)"),
("sinh---cosh_binary64", "(- f64 (cosh f64 ?x) (sinh f64 ?x))", "(exp f64 (neg f64 ?x))"),
("sinh-+-cosh_binary64", "(+ f64 (cosh f64 ?x) (sinh f64 ?x))", "(exp f64 ?x)"),
("sinh-cosh_binary64", "(- f64 (* f64 (cosh f64 ?x) (cosh f64 ?x)) (* f64 (sinh f64 ?x) (sinh f64 ?x)))", "1"),
("tanh-def-c_binary64", "(tanh f64 ?x)", "(/ f64 (- f64 1 (exp f64 (* f64 -2 ?x))) (+ f64 1 (exp f64 (* f64 -2 ?x))))"),
("tanh-def-b_binary64", "(tanh f64 ?x)", "(/ f64 (- f64 (exp f64 (* f64 2 ?x)) 1) (+ f64 (exp f64 (* f64 2 ?x)) 1))"),
("tanh-def-a_binary64", "(tanh f64 ?x)", "(/ f64 (- f64 (exp f64 ?x) (exp f64 (neg f64 ?x))) (+ f64 (exp f64 ?x) (exp f64 (neg f64 ?x))))"),
("cosh-def_binary64", "(cosh f64 ?x)", "(/ f64 (+ f64 (exp f64 ?x) (exp f64 (neg f64 ?x))) 2)"),
("sinh-def_binary64", "(sinh f64 ?x)", "(/ f64 (- f64 (exp f64 ?x) (exp f64 (neg f64 ?x))) 2)"),
("tan-neg_binary64", "(tan f64 (neg f64 ?x))", "(neg f64 (tan f64 ?x))"),
("cos-neg_binary64", "(cos f64 (neg f64 ?x))", "(cos f64 ?x)"),
("sin-neg_binary64", "(sin f64 (neg f64 ?x))", "(neg f64 (sin f64 ?x))"),
("tan-0_binary64", "(tan f64 0)", "0"),
("cos-0_binary64", "(cos f64 0)", "1"),
("sin-0_binary64", "(sin f64 0)", "0"),
("hang-m-tan_binary64", "(/ f64 (- f64 (sin f64 ?a) (sin f64 ?b)) (+ f64 (cos f64 ?a) (cos f64 ?b)))", "(tan f64 (/ f64 (- f64 ?a ?b) 2))"),
("hang-p-tan_binary64", "(/ f64 (+ f64 (sin f64 ?a) (sin f64 ?b)) (+ f64 (cos f64 ?a) (cos f64 ?b)))", "(tan f64 (/ f64 (+ f64 ?a ?b) 2))"),
("hang-m0-tan_binary64", "(/ f64 (- f64 1 (cos f64 ?a)) (neg f64 (sin f64 ?a)))", "(tan f64 (/ f64 (neg f64 ?a) 2))"),
("hang-p0-tan_binary64", "(/ f64 (- f64 1 (cos f64 ?a)) (sin f64 ?a))", "(tan f64 (/ f64 ?a 2))"),
("hang-0m-tan_binary64", "(/ f64 (neg f64 (sin f64 ?a)) (+ f64 1 (cos f64 ?a)))", "(tan f64 (/ f64 (neg f64 ?a) 2))"),
("hang-0p-tan_binary64", "(/ f64 (sin f64 ?a) (+ f64 1 (cos f64 ?a)))", "(tan f64 (/ f64 ?a 2))"),
("tan-+PI/2_binary64", "(tan f64 (+ f64 ?x (/ f64 (PI f64) 2)))", "(/ f64 -1 (tan f64 ?x))"),
("tan-+PI_binary64", "(tan f64 (+ f64 ?x (PI f64)))", "(tan f64 ?x)"),
("tan-PI_binary64", "(tan f64 (PI f64))", "0"),
("tan-PI/3_binary64", "(tan f64 (/ f64 (PI f64) 3))", "(sqrt f64 3)"),
("tan-PI/4_binary64", "(tan f64 (/ f64 (PI f64) 4))", "1"),
("tan-PI/6_binary64", "(tan f64 (/ f64 (PI f64) 6))", "(/ f64 1 (sqrt f64 3))"),
("cos-+PI/2_binary64", "(cos f64 (+ f64 ?x (/ f64 (PI f64) 2)))", "(neg f64 (sin f64 ?x))"),
("cos-+PI_binary64", "(cos f64 (+ f64 ?x (PI f64)))", "(neg f64 (cos f64 ?x))"),
("cos-PI_binary64", "(cos f64 (PI f64))", "-1"),
("cos-PI/2_binary64", "(cos f64 (/ f64 (PI f64) 2))", "0"),
("cos-PI/3_binary64", "(cos f64 (/ f64 (PI f64) 3))", "1/2"),
("cos-PI/4_binary64", "(cos f64 (/ f64 (PI f64) 4))", "(/ f64 (sqrt f64 2) 2)"),
("cos-PI/6_binary64", "(cos f64 (/ f64 (PI f64) 6))", "(/ f64 (sqrt f64 3) 2)"),
("sin-+PI/2_binary64", "(sin f64 (+ f64 ?x (/ f64 (PI f64) 2)))", "(cos f64 ?x)"),
("sin-+PI_binary64", "(sin f64 (+ f64 ?x (PI f64)))", "(neg f64 (sin f64 ?x))"),
("sin-PI_binary64", "(sin f64 (PI f64))", "0"),
("sin-PI/2_binary64", "(sin f64 (/ f64 (PI f64) 2))", "1"),
("sin-PI/3_binary64", "(sin f64 (/ f64 (PI f64) 3))", "(/ f64 (sqrt f64 3) 2)"),
("sin-PI/4_binary64", "(sin f64 (/ f64 (PI f64) 4))", "(/ f64 (sqrt f64 2) 2)"),
("sin-PI/6_binary64", "(sin f64 (/ f64 (PI f64) 6))", "1/2"),
("sub-1-sin_binary64", "(- f64 (* f64 (sin f64 ?a) (sin f64 ?a)) 1)", "(neg f64 (* f64 (cos f64 ?a) (cos f64 ?a)))"),
("sub-1-cos_binary64", "(- f64 (* f64 (cos f64 ?a) (cos f64 ?a)) 1)", "(neg f64 (* f64 (sin f64 ?a) (sin f64 ?a)))"),
("-1-add-sin_binary64", "(+ f64 (* f64 (sin f64 ?a) (sin f64 ?a)) -1)", "(neg f64 (* f64 (cos f64 ?a) (cos f64 ?a)))"),
("-1-add-cos_binary64", "(+ f64 (* f64 (cos f64 ?a) (cos f64 ?a)) -1)", "(neg f64 (* f64 (sin f64 ?a) (sin f64 ?a)))"),
("1-sub-sin_binary64", "(- f64 1 (* f64 (sin f64 ?a) (sin f64 ?a)))", "(* f64 (cos f64 ?a) (cos f64 ?a))"),
("1-sub-cos_binary64", "(- f64 1 (* f64 (cos f64 ?a) (cos f64 ?a)))", "(* f64 (sin f64 ?a) (sin f64 ?a))"),
("cos-sin-sum_binary64", "(+ f64 (* f64 (cos f64 ?a) (cos f64 ?a)) (* f64 (sin f64 ?a) (sin f64 ?a)))", "1"),
("log-E_binary64", "(log f64 (E f64))", "1"),
("log-pow_binary64", "(log f64 (pow f64 ?a ?b))", "(* f64 ?b (log f64 ?a))"),
("log-rec_binary64", "(log f64 (/ f64 1 ?a))", "(neg f64 (log f64 ?a))"),
("log-div_binary64", "(log f64 (/ f64 ?a ?b))", "(- f64 (log f64 ?a) (log f64 ?b))"),
("log-prod_binary64", "(log f64 (* f64 ?a ?b))", "(+ f64 (log f64 ?a) (log f64 ?b))"),
("pow-base-0_binary64", "(pow f64 0 ?a)", "0"),
("unpow1/3_binary64", "(pow f64 ?a 1/3)", "(cbrt f64 ?a)"),
("unpow3_binary64", "(pow f64 ?a 3)", "(* f64 (* f64 ?a ?a) ?a)"),
("unpow2_binary64", "(pow f64 ?a 2)", "(* f64 ?a ?a)"),
("unpow1/2_binary64", "(pow f64 ?a 1/2)", "(sqrt f64 ?a)"),
("pow-plus_binary64", "(* f64 (pow f64 ?a ?b) ?a)", "(pow f64 ?a (+ f64 ?b 1))"),
("exp-to-pow_binary64", "(exp f64 (* f64 (log f64 ?a) ?b))", "(pow f64 ?a ?b)"),
("pow-base-1_binary64", "(pow f64 1 ?a)", "1"),
("unpow0_binary64", "(pow f64 ?a 0)", "1"),
("unpow1_binary64", "(pow f64 ?a 1)", "?a"),
("unpow-1_binary64", "(pow f64 ?a -1)", "(/ f64 1 ?a)"),
("exp-lft-cube_binary64", "(exp f64 (* f64 ?a 3))", "(pow f64 (exp f64 ?a) 3)"),
("exp-lft-sqr_binary64", "(exp f64 (* f64 ?a 2))", "(* f64 (exp f64 ?a) (exp f64 ?a))"),
("exp-cbrt_binary64", "(exp f64 (/ f64 ?a 3))", "(cbrt f64 (exp f64 ?a))"),
("exp-sqrt_binary64", "(exp f64 (/ f64 ?a 2))", "(sqrt f64 (exp f64 ?a))"),
("exp-prod_binary64", "(exp f64 (* f64 ?a ?b))", "(pow f64 (exp f64 ?a) ?b)"),
("div-exp_binary64", "(/ f64 (exp f64 ?a) (exp f64 ?b))", "(exp f64 (- f64 ?a ?b))"),
("rec-exp_binary64", "(/ f64 1 (exp f64 ?a))", "(exp f64 (neg f64 ?a))"),
("prod-exp_binary64", "(* f64 (exp f64 ?a) (exp f64 ?b))", "(exp f64 (+ f64 ?a ?b))"),
("exp-diff_binary64", "(exp f64 (- f64 ?a ?b))", "(/ f64 (exp f64 ?a) (exp f64 ?b))"),
("exp-neg_binary64", "(exp f64 (neg f64 ?a))", "(/ f64 1 (exp f64 ?a))"),
("exp-sum_binary64", "(exp f64 (+ f64 ?a ?b))", "(* f64 (exp f64 ?a) (exp f64 ?b))"),
("e-exp-1_binary64", "(E f64)", "(exp f64 1)"),
("1-exp_binary64", "1", "(exp f64 0)"),
("exp-1-e_binary64", "(exp f64 1)", "(E f64)"),
("exp-0_binary64", "(exp f64 0)", "1"),
("rem-log-exp_binary64", "(log f64 (exp f64 ?x))", "?x"),
("rem-exp-log_binary64", "(exp f64 (log f64 ?x))", "?x"),
("cube-unmult_binary64", "(* f64 ?x (* f64 ?x ?x))", "(pow f64 ?x 3)"),
("cube-mult_binary64", "(pow f64 ?x 3)", "(* f64 ?x (* f64 ?x ?x))"),
("cube-div_binary64", "(pow f64 (/ f64 ?x ?y) 3)", "(/ f64 (pow f64 ?x 3) (pow f64 ?y 3))"),
("cube-prod_binary64", "(pow f64 (* f64 ?x ?y) 3)", "(* f64 (pow f64 ?x 3) (pow f64 ?y 3))"),
("cube-neg_binary64", "(pow f64 (neg f64 ?x) 3)", "(neg f64 (pow f64 ?x 3))"),
("rem-3cbrt-rft_binary64", "(* f64 (cbrt f64 ?x) (* f64 (cbrt f64 ?x) (cbrt f64 ?x)))", "?x"),
("rem-3cbrt-lft_binary64", "(* f64 (* f64 (cbrt f64 ?x) (cbrt f64 ?x)) (cbrt f64 ?x))", "?x"),
("rem-cbrt-cube_binary64", "(cbrt f64 (pow f64 ?x 3))", "?x"),
("rem-cube-cbrt_binary64", "(pow f64 (cbrt f64 ?x) 3)", "?x"),
("sqr-abs_binary64", "(* f64 (fabs f64 ?x) (fabs f64 ?x))", "(* f64 ?x ?x)"),
("sqr-neg_binary64", "(* f64 (neg f64 ?x) (neg f64 ?x))", "(* f64 ?x ?x)"),
("rem-sqrt-square_binary64", "(sqrt f64 (* f64 ?x ?x))", "(fabs f64 ?x)"),
("rem-square-sqrt_binary64", "(* f64 (sqrt f64 ?x) (sqrt f64 ?x))", "?x"),
("times-frac_binary64", "(/ f64 (* f64 ?a ?b) (* f64 ?c ?d))", "(* f64 (/ f64 ?a ?c) (/ f64 ?b ?d))"),
("div-sub_binary64", "(/ f64 (- f64 ?a ?b) ?c)", "(- f64 (/ f64 ?a ?c) (/ f64 ?b ?c))"),
("neg-mul-1_binary64", "(neg f64 ?a)", "(* f64 -1 ?a)"),
("neg-sub0_binary64", "(neg f64 ?b)", "(- f64 0 ?b)"),
("unsub-neg_binary64", "(+ f64 ?a (neg f64 ?b))", "(- f64 ?a ?b)"),
("sub-neg_binary64", "(- f64 ?a ?b)", "(+ f64 ?a (neg f64 ?b))"),
("mul-1-neg_binary64", "(* f64 -1 ?a)", "(neg f64 ?a)"),
("/-rgt-identity_binary64", "(/ f64 ?a 1)", "?a"),
("*-rgt-identity_binary64", "(* f64 ?a 1)", "?a"),
("*-lft-identity_binary64", "(* f64 1 ?a)", "?a"),
("remove-double-neg_binary64", "(neg f64 (neg f64 ?a))", "?a"),
("sub0-neg_binary64", "(- f64 0 ?a)", "(neg f64 ?a)"),
("--rgt-identity_binary64", "(- f64 ?a 0)", "?a"),
("+-rgt-identity_binary64", "(+ f64 ?a 0)", "?a"),
("+-lft-identity_binary64", "(+ f64 0 ?a)", "?a"),
("mul0-rgt_binary64", "(* f64 ?a 0)", "0"),
("mul0-lft_binary64", "(* f64 0 ?a)", "0"),
("div0_binary64", "(/ f64 0 ?a)", "0"),
("*-inverses_binary64", "(/ f64 ?a ?a)", "1"),
("+-inverses_binary64", "(- f64 ?a ?a)", "0"),
("lft-mult-inverse_binary64", "(* f64 (/ f64 1 ?a) ?a)", "1"),
("rgt-mult-inverse_binary64", "(* f64 ?a (/ f64 1 ?a))", "1"),
("remove-double-div_binary64", "(/ f64 1 (/ f64 1 ?a))", "?a"),
("pow-sqr_binary64", "(* f64 (pow f64 ?a ?b) (pow f64 ?a ?b))", "(pow f64 ?a (* f64 2 ?b))"),
("sqr-pow_binary64", "(pow f64 ?a ?b)", "(* f64 (pow f64 ?a (/ f64 ?b 2)) (pow f64 ?a (/ f64 ?b 2)))"),
("difference-of-sqr--1_binary64", "(+ f64 (* f64 ?a ?a) -1)", "(* f64 (+ f64 ?a 1) (- f64 ?a 1))"),
("difference-of-sqr-1_binary64", "(- f64 (* f64 ?a ?a) 1)", "(* f64 (+ f64 ?a 1) (- f64 ?a 1))"),
("difference-of-squares_binary64", "(- f64 (* f64 ?a ?a) (* f64 ?b ?b))", "(* f64 (+ f64 ?a ?b) (- f64 ?a ?b))"),
("unswap-sqr_binary64", "(* f64 (* f64 ?a ?a) (* f64 ?b ?b))", "(* f64 (* f64 ?a ?b) (* f64 ?a ?b))"),
("swap-sqr_binary64", "(* f64 (* f64 ?a ?b) (* f64 ?a ?b))", "(* f64 (* f64 ?a ?a) (* f64 ?b ?b))"),
("cancel-sign-sub-inv_binary64", "(- f64 ?a (* f64 ?b ?c))", "(+ f64 ?a (* f64 (neg f64 ?b) ?c))"),
("cancel-sign-sub_binary64", "(- f64 ?a (* f64 (neg f64 ?b) ?c))", "(+ f64 ?a (* f64 ?b ?c))"),
("distribute-neg-frac_binary64", "(neg f64 (/ f64 ?a ?b))", "(/ f64 (neg f64 ?a) ?b)"),
("distribute-frac-neg_binary64", "(/ f64 (neg f64 ?a) ?b)", "(neg f64 (/ f64 ?a ?b))"),
("distribute-neg-out_binary64", "(+ f64 (neg f64 ?a) (neg f64 ?b))", "(neg f64 (+ f64 ?a ?b))"),
("distribute-neg-in_binary64", "(neg f64 (+ f64 ?a ?b))", "(+ f64 (neg f64 ?a) (neg f64 ?b))"),
("distribute-rgt-neg-out_binary64", "(* f64 ?a (neg f64 ?b))", "(neg f64 (* f64 ?a ?b))"),
("distribute-lft-neg-out_binary64", "(* f64 (neg f64 ?a) ?b)", "(neg f64 (* f64 ?a ?b))"),
("distribute-rgt-neg-in_binary64", "(neg f64 (* f64 ?a ?b))", "(* f64 ?a (neg f64 ?b))"),
("distribute-lft-neg-in_binary64", "(neg f64 (* f64 ?a ?b))", "(* f64 (neg f64 ?a) ?b)"),
("distribute-rgt1-in_binary64", "(+ f64 ?a (* f64 ?c ?a))", "(* f64 (+ f64 ?c 1) ?a)"),
("distribute-lft1-in_binary64", "(+ f64 (* f64 ?b ?a) ?a)", "(* f64 (+ f64 ?b 1) ?a)"),
("distribute-rgt-out--_binary64", "(- f64 (* f64 ?b ?a) (* f64 ?c ?a))", "(* f64 ?a (- f64 ?b ?c))"),
("distribute-rgt-out_binary64", "(+ f64 (* f64 ?b ?a) (* f64 ?c ?a))", "(* f64 ?a (+ f64 ?b ?c))"),
("distribute-lft-out--_binary64", "(- f64 (* f64 ?a ?b) (* f64 ?a ?c))", "(* f64 ?a (- f64 ?b ?c))"),
("distribute-lft-out_binary64", "(+ f64 (* f64 ?a ?b) (* f64 ?a ?c))", "(* f64 ?a (+ f64 ?b ?c))"),
("distribute-rgt-in_binary64", "(* f64 ?a (+ f64 ?b ?c))", "(+ f64 (* f64 ?b ?a) (* f64 ?c ?a))"),
("distribute-lft-in_binary64", "(* f64 ?a (+ f64 ?b ?c))", "(+ f64 (* f64 ?a ?b) (* f64 ?a ?c))"),
("count-2_binary64", "(+ f64 ?x ?x)", "(* f64 2 ?x)"),
("associate-/l/_binary64", "(/ f64 (/ f64 ?b ?c) ?a)", "(/ f64 ?b (* f64 ?a ?c))"),
("associate-/r/_binary64", "(/ f64 ?a (/ f64 ?b ?c))", "(* f64 (/ f64 ?a ?b) ?c)"),
("associate-/l*_binary64", "(/ f64 (* f64 ?b ?c) ?a)", "(/ f64 ?b (/ f64 ?a ?c))"),
("associate-/r*_binary64", "(/ f64 ?a (* f64 ?b ?c))", "(/ f64 (/ f64 ?a ?b) ?c)"),
("associate-*l/_binary64", "(* f64 (/ f64 ?a ?b) ?c)", "(/ f64 (* f64 ?a ?c) ?b)"),
("associate-*r/_binary64", "(* f64 ?a (/ f64 ?b ?c))", "(/ f64 (* f64 ?a ?b) ?c)"),
("associate-*l*_binary64", "(* f64 (* f64 ?a ?b) ?c)", "(* f64 ?a (* f64 ?b ?c))"),
("associate-*r*_binary64", "(* f64 ?a (* f64 ?b ?c))", "(* f64 (* f64 ?a ?b) ?c)"),
("associate--r-_binary64", "(- f64 ?a (- f64 ?b ?c))", "(+ f64 (- f64 ?a ?b) ?c)"),
("associate--l-_binary64", "(- f64 (- f64 ?a ?b) ?c)", "(- f64 ?a (+ f64 ?b ?c))"),
("associate--l+_binary64", "(- f64 (+ f64 ?a ?b) ?c)", "(+ f64 ?a (- f64 ?b ?c))"),
("associate--r+_binary64", "(- f64 ?a (+ f64 ?b ?c))", "(- f64 (- f64 ?a ?b) ?c)"),
("associate-+l-_binary64", "(+ f64 (- f64 ?a ?b) ?c)", "(- f64 ?a (- f64 ?b ?c))"),
("associate-+r-_binary64", "(+ f64 ?a (- f64 ?b ?c))", "(- f64 (+ f64 ?a ?b) ?c)"),
("associate-+l+_binary64", "(+ f64 (+ f64 ?a ?b) ?c)", "(+ f64 ?a (+ f64 ?b ?c))"),
("associate-+r+_binary64", "(+ f64 ?a (+ f64 ?b ?c))", "(+ f64 (+ f64 ?a ?b) ?c)"),
("*-commutative_binary64", "(* f64 ?a ?b)", "(* f64 ?b ?a)"),
("+-commutative_binary64", "(+ f64 ?a ?b)", "(+ f64 ?b ?a)"),
],);

    rules
}

fn check_proof(
    r: &mut Runner,
    rules: Vec<Rewrite>,
    left: &str,
    right: &str,
    expected: Option<Vec<&str>>,
) {
    let rule_slice = &rules.iter().collect::<Vec<&Rewrite>>()[..];
    let proof = r.produce_proof(rule_slice, &left.parse().unwrap(), &right.parse().unwrap());
    match proof {
        Some(p) => {
            if let Some(e) = expected {
                assert_eq!(
                    Some(NodeExpr::<Math>::to_strings::<ConstantFold>(rule_slice, &p)),
                    Some(e.iter().map(|s| s.to_string()).collect())
                )
            } else {
                assert_eq!(
                    Some(NodeExpr::<Math>::to_strings::<ConstantFold>(rule_slice, &p)),
                    None
                )
            }
        }
        None => assert_eq!(None, expected),
    }
}

fn check_proof_exists(r: &mut Runner, rules: Vec<Rewrite>, left: &str, right: &str) {
    let rule_slice = &rules.iter().collect::<Vec<&Rewrite>>()[..];
    let proof = r.produce_proof(rule_slice, &left.parse().unwrap(), &right.parse().unwrap());
    match proof {
        Some(p) => {
            assert_ne!(p.len(), 0);
        }
        None => panic!("Expected proof, got None"),
    }
}

#[test]
fn herbie_prove_numerics() {
    let start: egg::RecExpr<_> =
        "(* f64 2 (atan f64 (sqrt f64 (/ f64 (- f64 1 h0) (+ f64 1 h0)))))"
            .parse()
            .unwrap();
    let mut runner = Runner::new(Default::default())
        .with_expr(&start)
        .with_node_limit(5000)
        .with_iter_limit(100_000_000) // should never hit
        .with_time_limit(Duration::from_secs(u64::MAX))
        .with_hook(|r| {
            if r.egraph.analysis.unsound.load(Ordering::SeqCst) {
                Err("Unsoundness detected".into())
            } else {
                Ok(())
            }
        });
    let first = "(+ f64 (neg f64 (neg f64 2)) 0))";
    let second = "-1";
    runner = runner.run(&math_rules());
    //assert!(runner.egraph.equivs(&first.parse().unwrap(), &second.parse().unwrap()).len() == 1);
    check_proof_exists(&mut runner, math_rules(), first, second);
}

#[test]
fn herbie_prove_2() {
    let start: egg::RecExpr<_> =
        "(* f64 2 (atan f64 (sqrt f64 (/ f64 (- f64 1 h0) (+ f64 1 h0)))))"
            .parse()
            .unwrap();
    let mut runner = Runner::new(Default::default())
        .with_expr(&start)
        .with_node_limit(5000)
        .with_iter_limit(100_000_000) // should never hit
        .with_time_limit(Duration::from_secs(u64::MAX))
        .with_hook(|r| {
            if r.egraph.analysis.unsound.load(Ordering::SeqCst) {
                Err("Unsoundness detected".into())
            } else {
                Ok(())
            }
        });
    let first = "2";
    let second = "(+ f64 1 1)";
    runner = runner.run(&math_rules());
    //assert!(runner.egraph.equivs(&first.parse().unwrap(), &second.parse().unwrap()).len() == 1);
    check_proof_exists(&mut runner, math_rules(), first, second);
}

#[test]
fn herbie_prove_neg() {
    let start: egg::RecExpr<_> =
        "(* f64 2 (atan f64 (sqrt f64 (/ f64 (- f64 1 h0) (+ f64 1 h0)))))"
            .parse()
            .unwrap();
    let mut runner = Runner::new(Default::default())
        .with_expr(&start)
        .with_node_limit(5000)
        .with_iter_limit(100_000_000) // should never hit
        .with_time_limit(Duration::from_secs(u64::MAX))
        .with_hook(|r| {
            if r.egraph.analysis.unsound.load(Ordering::SeqCst) {
                Err("Unsoundness detected".into())
            } else {
                Ok(())
            }
        });
    let first = "(neg f64 (neg f64 2)))";
    let second = "(neg f64 (neg f64 (+ f64 1 1))))";
    runner = runner.run(&math_rules());
    //assert!(runner.egraph.equivs(&first.parse().unwrap(), &second.parse().unwrap()).len() == 1);
    check_proof_exists(&mut runner, math_rules(), first, second);
}

#[test]
fn herbie_prove_small() {
    let start: egg::RecExpr<_> = "(/ f64 (- f64 (exp f64 h0) (exp f64 (neg f64 h0))) 2)"
        .parse()
        .unwrap();
    let mut runner = Runner::new(Default::default())
        .with_expr(&start)
        .with_node_limit(5000)
        .with_iter_limit(100_000_000) // should never hit
        .with_time_limit(Duration::from_secs(u64::MAX))
        .with_hook(|r| {
            if r.egraph.analysis.unsound.load(Ordering::SeqCst) {
                Err("Unsoundness detected".into())
            } else {
                Ok(())
            }
        });
    runner = runner.run(&math_rules());
    check_proof_exists(
        &mut runner,
        math_rules(),
        "(/ f64 (- f64 (exp f64 h0) (exp f64 (neg f64 h0))) 2)",
        "-1",
    );
}

#[test]
fn herbie_prove_long() {
    let start: egg::RecExpr<_> = "(biggroup (/ f64 -1 (pow f64 h0 3)) (/ f64 -1 (pow f64 h0 3)) (/ f64 -1 (pow f64 h0 3)) (/ f64 -1 (pow f64 h0 3)) (- f64 (/ f64 1 h0) (/ f64 1 (pow f64 h0 3))) (/ f64 1 h0) (- f64 (/ f64 1 h0) (/ f64 1 (pow f64 h0 3))) (/ f64 1 h0) (- f64 (/ f64 1 h0) (/ f64 1 (pow f64 h0 3))) (- f64 (log f64 -1) (* f64 (log f64 h0) 3)) (- f64 (log f64 -1) (* f64 (log f64 h0) 3)) (- f64 (log f64 -1) (log f64 (pow f64 h0 3))) (exp f64 (/ f64 -1 (pow f64 h0 3))) (log f64 (/ f64 -1 (pow f64 h0 3))) (* f64 (* f64 (/ f64 -1 (pow f64 h0 3)) (/ f64 -1 (pow f64 h0 3))) (/ f64 -1 (pow f64 h0 3))) (* f64 (cbrt f64 (/ f64 -1 (pow f64 h0 3))) (cbrt f64 (/ f64 -1 (pow f64 h0 3)))) (cbrt f64 (/ f64 -1 (pow f64 h0 3))) (/ f64 (* f64 (* f64 -1 -1) -1) (* f64 (* f64 (pow f64 h0 3) (pow f64 h0 3)) (pow f64 h0 3))) (sqrt f64 (/ f64 -1 (pow f64 h0 3))) (sqrt f64 (/ f64 -1 (pow f64 h0 3))) (neg f64 -1) (neg f64 (pow f64 h0 3)) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (pow f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 3)) (/ f64 (cbrt f64 -1) (pow f64 (cbrt f64 h0) 3)) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (pow f64 (sqrt f64 h0) 3)) (/ f64 (cbrt f64 -1) (pow f64 (sqrt f64 h0) 3)) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (pow f64 1 3)) (/ f64 (cbrt f64 -1) (pow f64 h0 3)) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (* f64 h0 h0)) (/ f64 (cbrt f64 -1) h0) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (* f64 (cbrt f64 (pow f64 h0 3)) (cbrt f64 (pow f64 h0 3)))) (/ f64 (cbrt f64 -1) (cbrt f64 (pow f64 h0 3))) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) h0) (/ f64 (cbrt f64 -1) (* f64 h0 h0)) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (pow f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 3)) (/ f64 (cbrt f64 -1) (pow f64 (cbrt f64 h0) 3)) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (pow f64 (sqrt f64 h0) 3)) (/ f64 (cbrt f64 -1) (pow f64 (sqrt f64 h0) 3)) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (pow f64 1 3)) (/ f64 (cbrt f64 -1) (pow f64 h0 3)) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (sqrt f64 (pow f64 h0 3))) (/ f64 (cbrt f64 -1) (sqrt f64 (pow f64 h0 3))) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) 1) (/ f64 (cbrt f64 -1) (pow f64 h0 3)) (/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (pow f64 h0 (/ f64 3 2))) (/ f64 (cbrt f64 -1) (pow f64 h0 (/ f64 3 2))) (/ f64 (sqrt f64 -1) (pow f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 3)) (/ f64 (sqrt f64 -1) (pow f64 (cbrt f64 h0) 3)) (/ f64 (sqrt f64 -1) (pow f64 (sqrt f64 h0) 3)) (/ f64 (sqrt f64 -1) (pow f64 (sqrt f64 h0) 3)) (/ f64 (sqrt f64 -1) (pow f64 1 3)) (/ f64 (sqrt f64 -1) (pow f64 h0 3)) (/ f64 (sqrt f64 -1) (* f64 h0 h0)) (/ f64 (sqrt f64 -1) h0) (/ f64 (sqrt f64 -1) (* f64 (cbrt f64 (pow f64 h0 3)) (cbrt f64 (pow f64 h0 3)))) (/ f64 (sqrt f64 -1) (cbrt f64 (pow f64 h0 3))) (/ f64 (sqrt f64 -1) h0) (/ f64 (sqrt f64 -1) (* f64 h0 h0)) (/ f64 (sqrt f64 -1) (pow f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 3)) (/ f64 (sqrt f64 -1) (pow f64 (cbrt f64 h0) 3)) (/ f64 (sqrt f64 -1) (pow f64 (sqrt f64 h0) 3)) (/ f64 (sqrt f64 -1) (pow f64 (sqrt f64 h0) 3)) (/ f64 (sqrt f64 -1) (pow f64 1 3)) (/ f64 (sqrt f64 -1) (pow f64 h0 3)) (/ f64 (sqrt f64 -1) (sqrt f64 (pow f64 h0 3))) (/ f64 (sqrt f64 -1) (sqrt f64 (pow f64 h0 3))) (/ f64 (sqrt f64 -1) 1) (/ f64 (sqrt f64 -1) (pow f64 h0 3)) (/ f64 (sqrt f64 -1) (pow f64 h0 (/ f64 3 2))) (/ f64 (sqrt f64 -1) (pow f64 h0 (/ f64 3 2))) (/ f64 1 (pow f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 3)) (/ f64 -1 (pow f64 (cbrt f64 h0) 3)) (/ f64 1 (pow f64 (sqrt f64 h0) 3)) (/ f64 -1 (pow f64 (sqrt f64 h0) 3)) (/ f64 1 (pow f64 1 3)) (/ f64 -1 (pow f64 h0 3)) (/ f64 1 (* f64 h0 h0)) (/ f64 -1 h0) (/ f64 1 (* f64 (cbrt f64 (pow f64 h0 3)) (cbrt f64 (pow f64 h0 3)))) (/ f64 -1 (cbrt f64 (pow f64 h0 3))) (/ f64 1 h0) (/ f64 -1 (* f64 h0 h0)) (/ f64 1 (pow f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 3)) (/ f64 -1 (pow f64 (cbrt f64 h0) 3)) (/ f64 1 (pow f64 (sqrt f64 h0) 3)) (/ f64 -1 (pow f64 (sqrt f64 h0) 3)) (/ f64 1 (pow f64 1 3)) (/ f64 -1 (pow f64 h0 3)) (/ f64 1 (sqrt f64 (pow f64 h0 3))) (/ f64 -1 (sqrt f64 (pow f64 h0 3))) (/ f64 1 1) (/ f64 -1 (pow f64 h0 3)) (/ f64 1 (pow f64 h0 (/ f64 3 2))) (/ f64 -1 (pow f64 h0 (/ f64 3 2))) (/ f64 (pow f64 h0 3) -1) (/ f64 1 (pow f64 h0 3)) (/ f64 (pow f64 h0 3) (cbrt f64 -1)) (/ f64 (pow f64 h0 3) (sqrt f64 -1)) (/ f64 (pow f64 h0 3) -1) (/ f64 -1 (pow f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 3)) (/ f64 -1 (pow f64 (sqrt f64 h0) 3)) (/ f64 -1 (pow f64 1 3)) (/ f64 -1 (* f64 h0 h0)) (/ f64 -1 (* f64 (cbrt f64 (pow f64 h0 3)) (cbrt f64 (pow f64 h0 3)))) (/ f64 -1 h0) (/ f64 -1 (pow f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 3)) (/ f64 -1 (pow f64 (sqrt f64 h0) 3)) (/ f64 -1 (pow f64 1 3)) (/ f64 -1 (sqrt f64 (pow f64 h0 3))) (/ f64 -1 1) (/ f64 -1 (pow f64 h0 (/ f64 3 2))) (* f64 (exp f64 (/ f64 1 h0)) (exp f64 (/ f64 -1 (pow f64 h0 3)))) (exp f64 (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3)))) (log f64 (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3)))) (* f64 (* f64 (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3))) (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3)))) (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3)))) (* f64 (cbrt f64 (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3)))) (cbrt f64 (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3))))) (cbrt f64 (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3)))) (sqrt f64 (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3)))) (sqrt f64 (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3)))) (+ f64 (* f64 1 (pow f64 h0 3)) (* f64 h0 -1)) (* f64 h0 (pow f64 h0 3)) (+ f64 (pow f64 (/ f64 1 h0) 3) (pow f64 (/ f64 -1 (pow f64 h0 3)) 3)) (+ f64 (* f64 (/ f64 1 h0) (/ f64 1 h0)) (- f64 (* f64 (/ f64 -1 (pow f64 h0 3)) (/ f64 -1 (pow f64 h0 3))) (* f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3))))) (- f64 (* f64 (/ f64 1 h0) (/ f64 1 h0)) (* f64 (/ f64 -1 (pow f64 h0 3)) (/ f64 -1 (pow f64 h0 3)))) (- f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3))) (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3))) (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3))) (+ f64 (/ f64 1 h0) (/ f64 -1 (pow f64 h0 3))))"
        .parse()
        .unwrap();
    let mut runner = Runner::new(Default::default())
        .with_expr(&start)
        .with_node_limit(5000)
        .with_iter_limit(100_000_000) // should never hit
        .with_time_limit(Duration::from_secs(u64::MAX))
        .with_hook(|r| {
            if r.egraph.analysis.unsound.load(Ordering::SeqCst) {
                Err("Unsoundness detected".into())
            } else {
                Ok(())
            }
        });
    runner = runner.run(&math_rules());
    check_proof_exists(
        &mut runner,
        math_rules(),
        "(/ f64 (* f64 (cbrt f64 -1) (cbrt f64 -1)) (pow f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 3))",
        "(/ f64 1 (* f64 h0 h0))",
    );
}

#[test]
fn herbie_prove_demo() {
    let start: egg::RecExpr<_> = "(biggroup (exp f64 (* f64 1/3 (+ f64 (log f64 h0) (log f64 (/ f64 1 h1))))) (exp f64 (* f64 1/3 (- f64 (log f64 (/ f64 1 h1)) (log f64 (/ f64 1 h0))))) (* f64 (exp f64 (* f64 1/3 (- f64 (log f64 (/ f64 1 h1)) (log f64 (/ f64 -1 h0))))) (cbrt f64 -1)) (exp f64 (* f64 1/3 (- f64 (log f64 h0) (log f64 h1)))) (exp f64 (* f64 1/3 (+ f64 (log f64 h0) (log f64 (/ f64 1 h1))))) (* f64 (exp f64 (* f64 1/3 (+ f64 (log f64 h0) (log f64 (/ f64 -1 h1))))) (cbrt f64 -1)) (exp f64 (* f64 1/3 (+ f64 (log f64 h0) (log f64 (/ f64 1 h1))))) (exp f64 (* f64 1/3 (- f64 (log f64 (/ f64 1 h1)) (log f64 (/ f64 1 h0))))) (* f64 (exp f64 (* f64 1/3 (- f64 (log f64 (/ f64 1 h1)) (log f64 (/ f64 -1 h0))))) (cbrt f64 -1)) (exp f64 (* f64 1/3 (- f64 (log f64 h0) (log f64 h1)))) (exp f64 (* f64 1/3 (+ f64 (log f64 h0) (log f64 (/ f64 1 h1))))) (* f64 (exp f64 (* f64 1/3 (+ f64 (log f64 h0) (log f64 (/ f64 -1 h1))))) (cbrt f64 -1)) (exp f64 (* f64 1/3 (+ f64 (log f64 h0) (log f64 (/ f64 1 h1))))) (exp f64 (* f64 1/3 (- f64 (log f64 (/ f64 1 h1)) (log f64 (/ f64 1 h0))))) (* f64 (exp f64 (* f64 1/3 (- f64 (log f64 (/ f64 1 h1)) (log f64 (/ f64 -1 h0))))) (cbrt f64 -1)) (exp f64 (* f64 1/3 (- f64 (log f64 h0) (log f64 h1)))) (exp f64 (* f64 1/3 (+ f64 (log f64 h0) (log f64 (/ f64 1 h1))))) (* f64 (exp f64 (* f64 1/3 (+ f64 (log f64 h0) (log f64 (/ f64 -1 h1))))) (cbrt f64 -1)) (exp f64 (* f64 1/3 (+ f64 (log f64 (/ f64 1 (pow f64 h1 2))) (* f64 2 (log f64 h0))))) (exp f64 (* f64 1/3 (- f64 (log f64 (/ f64 1 (pow f64 h1 2))) (* f64 2 (log f64 (/ f64 1 h0)))))) (* f64 (pow f64 (cbrt f64 -1) 2) (exp f64 (* f64 1/3 (- f64 (log f64 (/ f64 1 (pow f64 h1 2))) (* f64 2 (log f64 (/ f64 -1 h0))))))) (exp f64 (* f64 1/3 (- f64 (log f64 (pow f64 h0 2)) (* f64 2 (log f64 h1))))) (exp f64 (* f64 1/3 (+ f64 (log f64 (pow f64 h0 2)) (* f64 2 (log f64 (/ f64 1 h1)))))) (* f64 (exp f64 (* f64 1/3 (+ f64 (log f64 (pow f64 h0 2)) (* f64 2 (log f64 (/ f64 -1 h1)))))) (pow f64 (cbrt f64 -1) 2)) (exp f64 (cbrt f64 (/ f64 h0 h1))) (log f64 (cbrt f64 (/ f64 h0 h1))) (* f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (cbrt f64 (/ f64 h0 h1)))) (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 h0) (cbrt f64 h1) (cbrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 (cbrt f64 h0) (cbrt f64 h1))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (sqrt f64 h1))) (cbrt f64 (/ f64 (cbrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 1)) (cbrt f64 (/ f64 (cbrt f64 h0) h1)) (cbrt f64 (/ f64 (sqrt f64 h0) (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 (sqrt f64 h0) (cbrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) 1)) (cbrt f64 (/ f64 (sqrt f64 h0) h1)) (cbrt f64 (/ f64 1 (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 h0 (cbrt f64 h1))) (cbrt f64 (/ f64 1 (sqrt f64 h1))) (cbrt f64 (/ f64 h0 (sqrt f64 h1))) (cbrt f64 (/ f64 1 1)) (cbrt f64 (/ f64 h0 h1)) (cbrt f64 1) (cbrt f64 (/ f64 h0 h1)) (cbrt f64 h0) (cbrt f64 (/ f64 1 h1)) (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (exp f64 (cbrt f64 (/ f64 h0 h1))) (log f64 (cbrt f64 (/ f64 h0 h1))) (* f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (cbrt f64 (/ f64 h0 h1)))) (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 h0) (cbrt f64 h1) (cbrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 (cbrt f64 h0) (cbrt f64 h1))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (sqrt f64 h1))) (cbrt f64 (/ f64 (cbrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 1)) (cbrt f64 (/ f64 (cbrt f64 h0) h1)) (cbrt f64 (/ f64 (sqrt f64 h0) (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 (sqrt f64 h0) (cbrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) 1)) (cbrt f64 (/ f64 (sqrt f64 h0) h1)) (cbrt f64 (/ f64 1 (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 h0 (cbrt f64 h1))) (cbrt f64 (/ f64 1 (sqrt f64 h1))) (cbrt f64 (/ f64 h0 (sqrt f64 h1))) (cbrt f64 (/ f64 1 1)) (cbrt f64 (/ f64 h0 h1)) (cbrt f64 1) (cbrt f64 (/ f64 h0 h1)) (cbrt f64 h0) (cbrt f64 (/ f64 1 h1)) (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (exp f64 (cbrt f64 (/ f64 h0 h1))) (log f64 (cbrt f64 (/ f64 h0 h1))) (* f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (cbrt f64 (/ f64 h0 h1)))) (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 h0) (cbrt f64 h1) (cbrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 (cbrt f64 h0) (cbrt f64 h1))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (sqrt f64 h1))) (cbrt f64 (/ f64 (cbrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 1)) (cbrt f64 (/ f64 (cbrt f64 h0) h1)) (cbrt f64 (/ f64 (sqrt f64 h0) (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 (sqrt f64 h0) (cbrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) 1)) (cbrt f64 (/ f64 (sqrt f64 h0) h1)) (cbrt f64 (/ f64 1 (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 h0 (cbrt f64 h1))) (cbrt f64 (/ f64 1 (sqrt f64 h1))) (cbrt f64 (/ f64 h0 (sqrt f64 h1))) (cbrt f64 (/ f64 1 1)) (cbrt f64 (/ f64 h0 h1)) (cbrt f64 1) (cbrt f64 (/ f64 h0 h1)) (cbrt f64 h0) (cbrt f64 (/ f64 1 h1)) (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (* f64 (/ f64 h0 h1) (/ f64 h0 h1)) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (+ f64 1/3 1/3) (+ f64 1 1) (+ f64 1 1) (+ f64 (log f64 (cbrt f64 (/ f64 h0 h1))) (log f64 (cbrt f64 (/ f64 h0 h1)))) (exp f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (log f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (* f64 (* f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (cbrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))))) (cbrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (* f64 (/ f64 h0 h1) (/ f64 h0 h1)) (sqrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (sqrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 h0) (cbrt f64 h0)) (* f64 (cbrt f64 h1) (cbrt f64 h1)) (* f64 2 1/3) (* f64 2 1) (* f64 (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1)))) (* f64 (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1)))) (* f64 (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1)))) (* f64 (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1)))) (* f64 (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1)))) (* f64 (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1)))) (* f64 (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (* f64 (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (cbrt f64 (/ f64 h0 h1))))) (* f64 (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1)))) (cbrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))))) (* f64 (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (sqrt f64 (/ f64 h0 h1)))) 
    (* f64 (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (* f64 (cbrt f64 h1) (cbrt f64 h1))))) (* f64 (cbrt f64 (/ f64 (cbrt f64 h0) (cbrt f64 h1))) (cbrt f64 (/ f64 (cbrt f64 h0) (cbrt f64 h1)))) (* f64 (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (sqrt f64 h1))) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 (cbrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (cbrt f64 h0) (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 1)) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 1))) (* f64 (cbrt f64 (/ f64 (cbrt f64 h0) h1)) (cbrt f64 (/ f64 (cbrt f64 h0) h1))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 (sqrt f64 h0) (* f64 (cbrt f64 h1) (cbrt f64 h1))))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (cbrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (cbrt f64 h1)))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) 1)) (cbrt f64 (/ f64 (sqrt f64 h0) 1))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) h1)) (cbrt f64 (/ f64 (sqrt f64 h0) h1))) (* f64 (cbrt f64 (/ f64 1 (* f64 (cbrt f64 h1) (cbrt f64 h1)))) (cbrt f64 (/ f64 1 (* f64 (cbrt f64 h1) (cbrt f64 h1))))) (* f64 (cbrt f64 (/ f64 h0 (cbrt f64 h1))) (cbrt f64 (/ f64 h0 (cbrt f64 h1)))) (* f64 (cbrt f64 (/ f64 1 (sqrt f64 h1))) (cbrt f64 (/ f64 1 (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 h0 (sqrt f64 h1))) (cbrt f64 (/ f64 h0 (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 1 1)) (cbrt f64 (/ f64 1 1))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 1) (cbrt f64 1)) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 h0) (cbrt f64 h0)) (* f64 (cbrt f64 (/ f64 1 h1)) (cbrt f64 (/ f64 1 h1))) (* f64 (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (sqrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 1 1) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 h0) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 h0)) (* f64 (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (sqrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 (cbrt f64 h0) (cbrt f64 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 (cbrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 (cbrt f64 h0) h1)) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (cbrt f64 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 (sqrt f64 h0) h1)) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 h0 (cbrt f64 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 h0 (sqrt f64 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 1 h1)) (cbrt f64 (/ f64 h0 h1))) (* f64 (sqrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))) (* f64 (cbrt f64 (/ f64 h0 h1)) (* f64 (cbrt f64 (cbrt f64 (/ f64 h0 h1))) (cbrt f64 (cbrt f64 (/ f64 h0 h1))))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (sqrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (* f64 (cbrt f64 h1) (cbrt f64 h1))))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 (* f64 (cbrt f64 h0) (cbrt f64 h0)) 1))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 (sqrt f64 h0) (* f64 (cbrt f64 h1) (cbrt f64 h1))))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 (sqrt f64 h0) (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 (sqrt f64 h0) 1))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 1 (* f64 (cbrt f64 h1) (cbrt f64 h1))))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 1 (sqrt f64 h1)))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 1 1))) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 1)) (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 h0)) (* f64 (cbrt f64 (/ f64 h0 h1)) (sqrt f64 (cbrt f64 (/ f64 h0 h1)))) (* f64 (cbrt f64 (/ f64 h0 h1)) 1))"
        .parse()
        .unwrap();
    let mut runner = Runner::new(Default::default())
        .with_expr(&start)
        .with_node_limit(5000)
        .with_iter_limit(100_000_000) // should never hit
        .with_time_limit(Duration::from_secs(u64::MAX))
        .with_hook(|r| {
            if r.egraph.analysis.unsound.load(Ordering::SeqCst) {
                Err("Unsoundness detected".into())
            } else {
                Ok(())
            }
        });
    runner = runner.run(&math_rules());
    check_proof_exists(
        &mut runner,
        math_rules(),
        "(cbrt f64 (* f64 (cbrt f64 (/ f64 h0 h1)) (cbrt f64 (/ f64 h0 h1))))",
        "(cbrt f64 (cbrt f64 (pow f64 (/ f64 h0 h1) 2)))",
    );
}

#[test]
fn herbie_prove_cbrt() {
    let start: egg::RecExpr<_> = "(biggroup -1 (- f64 (* f64 2 (/ f64 h0 h1)) 1) (- f64 (* f64 2 (/ f64 h0 h1)) (+ f64 (* f64 2 (/ f64 (pow f64 h0 2) (pow f64 h1 2))) 1)) 1 (- f64 1 (* f64 2 (/ f64 h1 h0))) 1 (- f64 1 (* f64 2 (/ f64 h1 h0))) 1 (- f64 1 (* f64 2 (/ f64 h1 h0))) -1 (- f64 (* f64 2 (/ f64 h0 h1)) 1) (- f64 (* f64 2 (/ f64 h0 h1)) (+ f64 (* f64 2 (/ f64 (pow f64 h0 2) (pow f64 h1 2))) 1)) -1 (- f64 (* f64 2 (/ f64 h0 h1)) 1) (- f64 (* f64 2 (/ f64 h0 h1)) (+ f64 (* f64 2 (/ f64 (pow f64 h0 2) (pow f64 h1 2))) 1)) -1 (neg f64 (+ f64 (* f64 2 (/ f64 h0 h1)) 1)) (neg f64 (+ f64 (* f64 2 (/ f64 h0 h1)) (+ f64 (* f64 2 (/ f64 (pow f64 h0 2) (pow f64 h1 2))) 1))) 1 (+ f64 (* f64 2 (/ f64 h1 h0)) 1) 1 (+ f64 (* f64 2 (/ f64 h1 h0)) 1) 1 (+ f64 (* f64 2 (/ f64 h1 h0)) 1) -1 (neg f64 (+ f64 (* f64 2 (/ f64 h0 h1)) 1)) (neg f64 (+ f64 (* f64 2 (/ f64 h0 h1)) (+ f64 (* f64 2 (/ f64 (pow f64 h0 2) (pow f64 h1 2))) 1))) -1 (neg f64 (+ f64 (* f64 2 (/ f64 h0 h1)) 1)) (neg f64 (+ f64 (* f64 2 (/ f64 h0 h1)) (+ f64 (* f64 2 (/ f64 (pow f64 h0 2) (pow f64 h1 2))) 1))) (- f64 (log f64 (- f64 h0 h1)) (log f64 (+ f64 h1 h0))) (exp f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (log f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (* f64 (* f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (* f64 (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (* f64 (* f64 (- f64 h0 h1) (- f64 h0 h1)) (- f64 h0 h1)) (* f64 (* f64 (+ f64 h1 h0) (+ f64 h1 h0)) (+ f64 h1 h0))) (sqrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (sqrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (neg f64 (- f64 h0 h1)) (neg f64 (+ f64 h1 h0)) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) (sqrt f64 (+ f64 h1 h0))) (/ f64 (cbrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) 1) (/ f64 (cbrt f64 (- f64 h0 h1)) (+ f64 h1 h0)) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) 1) (/ f64 (cbrt f64 (- f64 h0 h1)) (+ f64 h1 h0)) (/ f64 (sqrt f64 (- f64 h0 h1)) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 (- f64 h0 h1)) (cbrt f64 (+ f64 h1 h0))) (/ f64 (sqrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0))) (/ f64 (sqrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0))) (/ f64 (sqrt f64 (- f64 h0 h1)) 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (+ f64 h1 h0)) (/ f64 (sqrt f64 (- f64 h0 h1)) 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (+ f64 h1 h0)) (/ f64 1 (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (- f64 h0 h1) (cbrt f64 (+ f64 h1 h0))) (/ f64 1 (sqrt f64 (+ f64 h1 h0))) (/ f64 (- f64 h0 h1) (sqrt f64 (+ f64 h1 h0))) (/ f64 1 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0)) (/ f64 1 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0)) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (cbrt f64 (+ f64 h1 h0))) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) (sqrt f64 (+ f64 h1 h0))) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (sqrt f64 (+ f64 h1 h0))) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) 1) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (+ f64 h1 h0)) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) 1) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (+ f64 h1 h0)) (/ f64 1 (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (- f64 h0 h1) (cbrt f64 (+ f64 h1 h0))) (/ f64 1 (sqrt f64 (+ f64 h1 h0))) (/ f64 (- f64 h0 h1) (sqrt f64 (+ f64 h1 h0))) (/ f64 1 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0)) (/ f64 1 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0)) (/ f64 h0 (+ f64 h1 h0)) (/ f64 h1 (+ f64 h1 h0)) (/ f64 (+ f64 h1 h0) (- f64 h0 h1)) (/ f64 1 (+ f64 h1 h0)) (* f64 (+ f64 h1 h0) (+ f64 (* f64 h0 h0) (+ f64 (* f64 h1 h1) (* f64 h0 h1)))) (* f64 (+ f64 h1 h0) (+ f64 h0 h1)) (/ f64 (- f64 h0 h1) (+ f64 (pow f64 h1 3) (pow f64 h0 3))) (/ f64 (- f64 h0 h1) (- f64 (* f64 h1 h1) (* f64 h0 h0))) (/ f64 (+ f64 h1 h0) (cbrt f64 (- f64 h0 h1))) (/ f64 (+ f64 h1 h0) (sqrt f64 (- f64 h0 h1))) (/ f64 (+ f64 h1 h0) (- f64 h0 h1)) (/ f64 (+ f64 h1 h0) (- f64 (sqrt f64 h0) (sqrt f64 h1))) (/ f64 (+ f64 h1 h0) (- f64 h0 h1)) (/ f64 (- f64 h0 h1) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (- f64 h0 h1) (sqrt f64 (+ f64 h1 h0))) (/ f64 (- f64 h0 h1) 1) (/ f64 (- f64 h0 h1) 1) (neg f64 1) (- f64 0 (- f64 (log f64 (- f64 h0 h1)) (log f64 (+ f64 h1 h0)))) (- f64 0 (log f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (- f64 (log f64 1) (- f64 (log f64 (- f64 h0 h1)) (log f64 (+ f64 h1 h0)))) (- f64 (log f64 1) (log f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (neg f64 (- f64 (log f64 (- f64 h0 h1)) (log f64 (+ f64 h1 h0)))) (neg f64 (log f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (exp f64 (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (log f64 (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (* f64 (* f64 (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (* f64 (cbrt f64 (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (cbrt f64 (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))))) (cbrt f64 (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 (* f64 (* f64 1 1) 1) (* f64 (* f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 (* f64 (* f64 1 1) 1) (/ f64 (* f64 (* f64 (- f64 h0 h1) (- f64 h0 h1)) (- f64 h0 h1)) (* f64 (* f64 (+ f64 h1 h0) (+ f64 h1 h0)) (+ f64 h1 h0)))) (sqrt f64 (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (sqrt f64 (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (neg f64 1) (neg f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (* f64 (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))))) (/ f64 (cbrt f64 1) (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (sqrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 (cbrt f64 1) (sqrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 (cbrt f64 1) (/ f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (cbrt f64 1) (/ f64 (cbrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) 1)) (/ f64 (cbrt f64 1) (/ f64 (cbrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) 1)) (/ f64 (cbrt f64 1) (/ f64 (cbrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (sqrt f64 (- f64 h0 h1)) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 (cbrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (sqrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (cbrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (sqrt f64 (- f64 h0 h1)) 1)) (/ f64 (cbrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (sqrt f64 (- f64 h0 h1)) 1)) (/ f64 (cbrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 1 (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 (cbrt f64 1) (/ f64 (- f64 h0 h1) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 1 (sqrt f64 (+ f64 h1 h0)))) (/ f64 (cbrt f64 1) (/ f64 (- f64 h0 h1) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 1 1)) (/ f64 (cbrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 1 1)) (/ f64 (cbrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 (cbrt f64 1) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (cbrt f64 1) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) 1)) (/ f64 (cbrt f64 1) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) 1)) (/ f64 (cbrt f64 1) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 1 (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 (cbrt f64 1) (/ f64 (- f64 h0 h1) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 1 (sqrt f64 (+ f64 h1 h0)))) (/ f64 (cbrt f64 1) (/ f64 (- f64 h0 h1) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 1 1)) (/ f64 (cbrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 1 1)) (/ f64 (cbrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) 1)
(/ f64 (cbrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (- f64 h0 h1)) (/ f64 (cbrt f64 1) (/ f64 1 (+ f64 h1 h0))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (- f64 h0 h1) (+ f64 (pow f64 h1 3) (pow f64 h0 3)))) (/ f64 (cbrt f64 1) (+ f64 (* f64 h1 h1) (- f64 (* f64 h0 h0) (* f64 h1 h0)))) (/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (/ f64 (- f64 h0 h1) (- f64 (* f64 h1 h1) (* f64 h0 h0)))) (/ f64 (cbrt f64 1) (- f64 h1 h0)) (/ f64 (sqrt f64 1) (* f64 (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))))) (/ f64 (sqrt f64 1) (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (sqrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (sqrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 (sqrt f64 1) (/ f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (cbrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) 1)) (/ f64 (sqrt f64 1) (/ f64 (cbrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) 1)) (/ f64 (sqrt f64 1) (/ f64 (cbrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 (sqrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) 1)) (/ f64 (sqrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) 1)) (/ f64 (sqrt f64 1) (/ f64 (sqrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (/ f64 1 (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 1 (sqrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 1 1)) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (/ f64 1 1)) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 (sqrt f64 1) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) 1)) (/ f64 (sqrt f64 1) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) 1)) (/ f64 (sqrt f64 1) (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (/ f64 1 (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (cbrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 1 (sqrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (sqrt f64 (+ f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 1 1)) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (/ f64 1 1)) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) 1) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (- f64 h0 h1)) (/ f64 (sqrt f64 1) (/ f64 1 (+ f64 h1 h0))) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (+ f64 (pow f64 h1 3) (pow f64 h0 3)))) (/ f64 (sqrt f64 1) (+ f64 (* f64 h1 h1) (- f64 (* f64 h0 h0) (* f64 h1 h0)))) (/ f64 (sqrt f64 1) (/ f64 (- f64 h0 h1) (- f64 (* f64 h1 h1) (* f64 h0 h0)))) (/ f64 (sqrt f64 1) (- f64 h1 h0)) (/ f64 1 (* f64 (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))))) (/ f64 1 (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 1 (sqrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 1 (sqrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 1 (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 1 (/ f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (cbrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) 1)) (/ f64 1 (/ f64 (cbrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 1 (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) 1)) (/ f64 1 (/ f64 (cbrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) 1)) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) 1)) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) (+ f64 h1 h0))) (/ f64 1 (/ f64 1 (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 1 (/ f64 (- f64 h0 h1) (cbrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 1 (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (- f64 h0 h1) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 1 1)) (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 1 (/ f64 1 1)) (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 1 (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 1 (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (cbrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) 1)) (/ f64 1 (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (+ f64 h1 h0))) (/ f64 1 (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) 1)) (/ f64 1 (/ f64 (- f64 (sqrt f64 h0) (sqrt f64 h1)) (+ f64 h1 h0))) (/ f64 1 (/ f64 1 (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 1 (/ f64 (- f64 h0 h1) (cbrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 1 (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (- f64 h0 h1) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 1 1)) (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 1 (/ f64 1 1)) (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 1 1) (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 1 (- f64 h0 h1)) (/ f64 1 (/ f64 1 (+ f64 h1 h0))) (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 (pow f64 h1 3) (pow f64 h0 3)))) (/ f64 1 (+ f64 (* f64 h1 h1) (- f64 (* f64 h0 h0) (* f64 h1 h0)))) (/ f64 1 (/ f64 (- f64 h0 h1) (- f64 (* f64 h1 h1) (* f64 h0 h0)))) (/ f64 1 (- f64 h1 h0)) (/ f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)) 1) (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (/ f64 1 (- f64 h0 h1)) (/ f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)) (cbrt f64 1)) (/ f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)) (sqrt f64 1)) (/ f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)) 1) (/ f64 1 (* f64 (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))))) (/ f64 1 (sqrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))) (/ f64 1 (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 1 (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) 1)) (/ f64 1 (/ f64 (* f64 (cbrt f64 (- f64 h0 h1)) (cbrt f64 (- f64 h0 h1))) 1)) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) 1)) (/ f64 1 (/ f64 (sqrt f64 (- f64 h0 h1)) 1)) (/ f64 1 (/ f64 1 (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 1 (/ f64 1 (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 1 1)) (/ f64 1 (/ f64 1 1)) (/ f64 1 (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 1 (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) 1)) (/ f64 1 (/ f64 (+ f64 (sqrt f64 h0) (sqrt f64 h1)) 1)) (/ f64 1 (/ f64 1 (* f64 (cbrt f64 (+ f64 h1 h0)) (cbrt f64 (+ f64 h1 h0))))) (/ f64 1 (/ f64 1 (sqrt f64 (+ f64 h1 h0)))) (/ f64 1 (/ f64 1 1)) (/ f64 1 (/ f64 1 1)) (/ f64 1 1) (/ f64 1 (- f64 h0 h1)) (/ f64 1 (/ f64 (- f64 h0 h1) (+ f64 (pow f64 h1 3) (pow f64 h0 3)))) (/ f64 1 (/ f64 (- f64 h0 h1) (- f64 (* f64 h1 h1) (* f64 h0 h0)))))"
        .parse()
        .unwrap();
    let mut runner = Runner::new(Default::default())
        .with_expr(&start)
        .with_node_limit(5000)
        .with_iter_limit(100_000_000) // should never hit
        .with_time_limit(Duration::from_secs(u64::MAX))
        .with_hook(|r| {
            if r.egraph.analysis.unsound.load(Ordering::SeqCst) {
                Err("Unsoundness detected".into())
            } else {
                Ok(())
            }
        });
    runner = runner.run(&math_rules());
    check_proof_exists(
        &mut runner,
        math_rules(),
        "(cbrt f64 1)",
        "(cbrt f64 (* f64 1 (* f64 1 1)))",
    );
}

//(/ f64 (* f64 (cbrt f64 1) (cbrt f64 1)) (* f64 (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0))) (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h1 h0)))))"" ""(/ f64 1 (* f64 (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h0 h1))) (cbrt f64 (/ f64 (- f64 h0 h1) (+ f64 h0 h1)))))
