use egg::{rewrite as rw, *};
use ordered_float::NotNan;

pub type EGraph = egg::EGraph<Math, ConstantFold>;
pub type Rewrite = egg::Rewrite<Math, ConstantFold>;

pub type Constant = NotNan<f64>;

define_language! {
    pub enum Math {
        "d" = Diff([Id; 2]),
        "i" = Integral([Id; 2]),

        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        "ln" = Ln(Id),
        "sqrt" = Sqrt(Id),

        "sin" = Sin(Id),
        "cos" = Cos(Id),

        Constant(Constant),
        Symbol(Symbol),
    }
}

// You could use egg::AstSize, but this is useful for debugging, since
// it will really try to get rid of the Diff operator
pub struct MathCostFn;
impl egg::CostFunction<Math> for MathCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &Math, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            Math::Diff(..) => 100,
            Math::Integral(..) => 100,
            _ => 1,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

#[derive(Default)]
pub struct ConstantFold;
impl Analysis<Math> for ConstantFold {
    type Data = Option<(Constant, PatternAst<Math>)>;

    fn merge(&self, to: &mut Self::Data, from: Self::Data) -> bool {
        if let (Some(c1), Some(c2)) = (to.as_ref(), from.as_ref()) {
            assert_eq!(c1.0, c2.0);
        }
        merge_if_different(to, to.clone().or(from.clone()))
    }

    fn make(egraph: &EGraph, enode: &Math) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.clone().map(|x| x.0);
        Some((
            match enode {
                Math::Constant(c) => *c,
                Math::Add([a, b]) => x(a)? + x(b)?,
                Math::Sub([a, b]) => x(a)? - x(b)?,
                Math::Mul([a, b]) => x(a)? * x(b)?,
                Math::Div([a, b]) if x(b) != Some(0.0.into()) => x(a)? / x(b)?,
                _ => return None,
            },
            {
                let mut pattern: PatternAst<Math> = Default::default();
                enode.for_each(|child| {
                    pattern.add(ENodeOrVar::ENode(Math::Constant(x(&child).unwrap())));
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

    fn modify(egraph: &mut EGraph, class_id: Id) {
        let class = &mut egraph[class_id];
        if let Some((c, node)) = class.data.clone() {
            let added = egraph.add(Math::Constant(c));
            let (id, did_something) = egraph.union(class_id, added);
            if did_something {
                let mut const_pattern: PatternAst<Math> = Default::default();
                const_pattern.add(ENodeOrVar::ENode(Math::Constant(c)));
                println!("using ids {} and {}", added, class_id);
                egraph.add_union_proof(
                    class_id,
                    added,
                    node,
                    const_pattern,
                    Default::default(),
                    "metadata-eval".to_string(),
                );
            }
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            assert!(
                !egraph[id].nodes.is_empty(),
                "empty eclass! {:#?}",
                egraph[id]
            );
            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

fn is_const_or_distinct_var(v: &str, w: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let v = v.parse().unwrap();
    let w = w.parse().unwrap();
    move |egraph, _, subst| {
        egraph.find(subst[v]) != egraph.find(subst[w])
            && egraph[subst[v]]
                .nodes
                .iter()
                .any(|n| matches!(n, Math::Constant(..) | Math::Symbol(..)))
    }
}

fn is_const(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        egraph[subst[var]]
            .nodes
            .iter()
            .any(|n| matches!(n, Math::Constant(..)))
    }
}

fn is_sym(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        egraph[subst[var]]
            .nodes
            .iter()
            .any(|n| matches!(n, Math::Symbol(..)))
    }
}

fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let zero = Math::Constant(0.0.into());
    move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> { vec![
    rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
    rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
    rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

    rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    rw!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))" if is_not_zero("?b")),
    // rw!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
    // rw!("canon-div"; "(* ?a (pow ?b -1))" => "(/ ?a ?b)" if is_not_zero("?b")),

    rw!("zero-add"; "(+ ?a 0)" => "?a"),
    rw!("zero-mul"; "(* ?a 0)" => "0"),
    rw!("one-mul";  "(* ?a 1)" => "?a"),

    rw!("add-zero"; "?a" => "(+ ?a 0)"),
    rw!("mul-one";  "?a" => "(* ?a 1)"),

    rw!("cancel-sub"; "(- ?a ?a)" => "0"),
    rw!("cancel-div"; "(/ ?a ?a)" => "1" if is_not_zero("?a")),

    rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
    rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

    rw!("pow-mul"; "(* (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (+ ?b ?c))"),
    rw!("pow0"; "(pow ?x 0)" => "1"
        if is_not_zero("?x")),
    rw!("pow1"; "(pow ?x 1)" => "?x"),
    rw!("pow2"; "(pow ?x 2)" => "(* ?x ?x)"),
    rw!("pow-recip"; "(pow ?x -1)" => "(/ 1 ?x)"
        if is_not_zero("?x")),
    rw!("recip-mul-div"; "(* ?x (/ 1 ?x))" => "1" if is_not_zero("?x")),

    rw!("d-variable"; "(d ?x ?x)" => "1" if is_sym("?x")),
    rw!("d-constant"; "(d ?x ?c)" => "0" if is_sym("?x") if is_const_or_distinct_var("?c", "?x")),

    rw!("d-add"; "(d ?x (+ ?a ?b))" => "(+ (d ?x ?a) (d ?x ?b))"),
    rw!("d-mul"; "(d ?x (* ?a ?b))" => "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))"),

    rw!("d-sin"; "(d ?x (sin ?x))" => "(cos ?x)"),
    rw!("d-cos"; "(d ?x (cos ?x))" => "(* -1 (sin ?x))"),

    rw!("d-ln"; "(d ?x (ln ?x))" => "(/ 1 ?x)" if is_not_zero("?x")),

    rw!("d-power";
        "(d ?x (pow ?f ?g))" =>
        "(* (pow ?f ?g)
            (+ (* (d ?x ?f)
                  (/ ?g ?f))
               (* (d ?x ?g)
                  (ln ?f))))"
        if is_not_zero("?f")
        if is_not_zero("?g")
    ),

    rw!("i-one"; "(i 1 ?x)" => "?x"),
    rw!("i-power-const"; "(i (pow ?x ?c) ?x)" =>
        "(/ (pow ?x (+ ?c 1)) (+ ?c 1))" if is_const("?c")),
    rw!("i-cos"; "(i (cos ?x) ?x)" => "(sin ?x)"),
    rw!("i-sin"; "(i (sin ?x) ?x)" => "(* -1 (cos ?x))"),
    rw!("i-sum"; "(i (+ ?f ?g) ?x)" => "(+ (i ?f ?x) (i ?g ?x))"),
    rw!("i-dif"; "(i (- ?f ?g) ?x)" => "(- (i ?f ?x) (i ?g ?x))"),
    rw!("i-parts"; "(i (* ?a ?b) ?x)" =>
        "(- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x))"),
]}

egg::test_fn! {
    math_associate_adds, [
        rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    ],
    runner = Runner::default()
        .with_iter_limit(7)
        .with_scheduler(SimpleScheduler),
    "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))"
    =>
    "(+ 7 (+ 6 (+ 5 (+ 4 (+ 3 (+ 2 1))))))"
    @check |r: Runner<Math, ()>| assert_eq!(r.egraph.number_of_classes(), 127)
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    math_fail, rules(),
    "(+ x y)" => "(/ x y)"
}

egg::test_fn! {math_simplify_add, rules(), "(+ x (+ x (+ x x)))" => "(* 4 x)" }
egg::test_fn! {math_powers, rules(), "(* (pow 2 x) (pow 2 y))" => "(pow 2 (+ x y))"}

egg::test_fn! {
    math_simplify_const, rules(),
    "(+ 1 (- a (* (- 2 1) a)))" => "1"
}

egg::test_fn! {
    math_simplify_root, rules(),
    runner = Runner::default().with_node_limit(75_000),
    r#"
    (/ 1
       (- (/ (+ 1 (sqrt five))
             2)
          (/ (- 1 (sqrt five))
             2)))"#
    =>
    "(/ 1 (sqrt five))"
}

egg::test_fn! {
    math_simplify_factor, rules(),
    "(* (+ x 3) (+ x 1))"
    =>
    "(+ (+ (* x x) (* 4 x)) 3)"
}

egg::test_fn! {math_diff_same,      rules(), "(d x x)" => "1"}
egg::test_fn! {math_diff_different, rules(), "(d x y)" => "0"}
egg::test_fn! {math_diff_simple1,   rules(), "(d x (+ 1 (* 2 x)))" => "2"}
egg::test_fn! {math_diff_simple2,   rules(), "(d x (+ 1 (* y x)))" => "y"}
egg::test_fn! {math_diff_ln,        rules(), "(d x (ln x))" => "(/ 1 x)"}

egg::test_fn! {
    diff_power_simple, rules(),
    "(d x (pow x 3))" => "(* 3 (pow x 2))"
}

egg::test_fn! {
    diff_power_harder, rules(),
    runner = Runner::default()
        .with_time_limit(std::time::Duration::from_secs(10))
        .with_iter_limit(60)
        .with_node_limit(100_000)
        // HACK this needs to "see" the end expression
        .with_expr(&"(* x (- (* 3 x) 14))".parse().unwrap()),
    "(d x (- (pow x 3) (* 7 (pow x 2))))"
    =>
    "(* x (- (* 3 x) 14))"
}

egg::test_fn! {
    integ_one, rules(), "(i 1 x)" => "x"
}

egg::test_fn! {
    integ_sin, rules(), "(i (cos x) x)" => "(sin x)"
}

egg::test_fn! {
    integ_x, rules(), "(i (pow x 1) x)" => "(/ (pow x 2) 2)"
}

egg::test_fn! {
    integ_part1, rules(), "(i (* x (cos x)) x)" => "(+ (* x (sin x)) (cos x))"
}

egg::test_fn! {
    integ_part2, rules(),
    "(i (* (cos x) x) x)" => "(+ (* x (sin x)) (cos x))"
}

egg::test_fn! {
    integ_part3, rules(), "(i (ln x) x)" => "(- (* x (ln x)) x)"
}

// Proof tests
#[rustfmt::skip]
pub fn simple_rules() -> Vec<Rewrite> { vec![
    rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
]}

fn check_proof(
    r: &mut Runner<Math, ConstantFold>,
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

fn check_proof_exists(
    r: &mut Runner<Math, ConstantFold>,
    rules: Vec<Rewrite>,
    left: &str,
    right: &str,
) {
    let rule_slice = &rules.iter().collect::<Vec<&Rewrite>>()[..];
    let proof = r.produce_proof(rule_slice, &left.parse().unwrap(), &right.parse().unwrap());
    match proof {
        Some(p) => {
            assert_ne!(p.len(), 0);
        }
        None => panic!("Expected proof, got None"),
    }
}

egg::test_fn! {
    math_prove, simple_rules(),
    runner = Runner::default()
        .with_iter_limit(1)
        .with_scheduler(SimpleScheduler),
    "(+ a b)"
    =>
    "(+ b a)"
    @check |mut r: Runner<Math, ConstantFold>| {
        r.egraph.dot().to_png("target/tree.png").unwrap();
        check_proof(&mut r, simple_rules(), "(+ a b)", "(+ b a)",
                    Some(vec!["(=> (+ a b))",
                         "comm-add =>",
                         "(+ b a)"]));
    }
}

egg::test_fn! {
    math_prove_children, simple_rules(),
    runner = Runner::default()
        .with_iter_limit(7)
        .with_scheduler(SimpleScheduler),
    "(+ a (+ b c))"
    =>
    "(+ a (+ c b))"
    @check |mut r: Runner<Math, ConstantFold>| {
        check_proof(&mut r, simple_rules(), "(+ a (+ b c))",
                    "(+ a (+ c b))",
                    Some(vec!["(+ a (=> (+ b c)))", "comm-add =>", "(+ a (+ c b))"]));
    }
}

egg::test_fn! {
    math_prove_multiple, rules(),
    runner = Runner::default()
        .with_iter_limit(7)
        .with_scheduler(SimpleScheduler),
    "(+ a (+ b c))"
    =>
    "(+ (+ a c) b))"
    @check |mut r: Runner<Math, ConstantFold>| {
        check_proof(&mut r, rules(), "(+ a (+ b c))",
                    "(+ (+ a c) b))",
                    Some(vec!["(+ a (=> (+ b c)))",
                         "comm-add =>",
                         "(=> (+ a (+ c b)))",
                         "assoc-add =>",
                         "(+ (+ a c) b)"]));
    }
}

egg::test_fn! {
    math_prove_simple_match_single_var, rules(),
    "a" => "(+ (+ (+ a 0) 0) 0)"
    @check |mut r: Runner<Math, ConstantFold>| {
        check_proof(&mut r, rules(), "a",
                    "(+ (+ (+ a 0) 0) 0)",
                    Some(vec!["(=> a)", "add-zero =>", "(+ (=> a) 0)", "add-zero =>",
                         "(+ (+ (=> a) 0) 0)", "add-zero =>", "(+ (+ (+ a 0) 0) 0)"]));
    }
}

egg::test_fn! {
    math_prove_simple_match_single_var_backwards, rules(),
    "a" => "(+ (+ (+ a 0) 0) 0)"
    @check |mut r: Runner<Math, ConstantFold>| {
        check_proof(&mut r, rules(), "(+ (+ (+ a 0) 0) 0)",
                    "a",
                    Some(vec!["(+ (+ (+ a 0) 0) 0)", "<= add-zero", "(<= (+ (+ a 0) 0))", "<= add-zero", "(<= (+ a 0))", "<= add-zero", "(<= a)"]));
    }
}

egg::test_fn! {
    math_prove_simplify_const, rules(),
    runner = Runner::default()
        .with_iter_limit(2)
        .with_scheduler(SimpleScheduler),
        "(+ 1 (- a (* (- 2 1) a)))" => "1"
    @check |mut r: Runner<Math, ConstantFold>| {
        //r.egraph.dot().to_png("target/newegraph.png").unwrap();
        check_proof(&mut r, rules(), "(+ 1 (- a (* (- 2 1) a)))",
                                    "1",
                                    Some(vec!["(+ 1 (- a (=> (* (- 2 1) a))))",
                                          "comm-mul =>",
                                          "(+ 1 (- a (* a (=> (- 2 1)))))",
                                          "metadata-eval =>",
                                          "(+ 1 (- a (* a 1)))",
                                          "<= mul-one",
                                          "(+ 1 (=> (- a (<= a))))",
                                          "cancel-sub =>",
                                          "(=> (+ 1 0))",
                                          "metadata-eval =>",
                                          "1"]));
    }
}

egg::test_fn! {
    math_prove_simplify_const_backwards, rules(),
    runner = Runner::default()
        .with_iter_limit(2)
        .with_scheduler(SimpleScheduler),
    "(+ 1 (- a (* (- 2 1) a)))" => "1"
    @check |mut r: Runner<Math, ConstantFold>| {
        println!("running proof");
        check_proof(&mut r, rules(), "1",
                        "(+ 1 (- a (* (- 2 1) a)))",
                        Some(vec!["1", "<= metadata-eval", "(<= (+ 1 0))", "<= cancel-sub", "(+ 1 (<= (- a (=> a))))", "mul-one =>", "(+ 1 (- a (* a 1)))", "<= comm-mul", "(+ 1 (- a (<= (* 1 a))))", "<= metadata-eval", "(+ 1 (- a (* (<= (- 2 1)) a)))"]));
    }
}

egg::test_fn! {
    math_prove_integ_x, rules(),
    runner = Runner::default()
                     .with_iter_limit(10)
                     .with_scheduler(SimpleScheduler),
    "(i (pow x 1) x)" => "(/ (pow x 2) 2)"
    @check |mut r: Runner<Math, ConstantFold>| {
        check_proof(&mut r, rules(), "(i (pow x 1) x)", "(/ (pow x 2) 2)",
                    Some(vec!["(=> (i (pow x 1) x))", "i-power-const =>", "(/ (pow x (=> (+ 1 1))) (+ 1 1))", "metadata-eval =>", "(/ (pow x 2) (=> (+ 1 1)))", "metadata-eval =>", "(/ (pow x 2) 2)"]));
    }
}

egg::test_fn! {
    math_prove_integ_part2_smaller, rules(),
    runner = Runner::default()
             .with_iter_limit(7),
    "(i (* (cos x) x) x)" => "(+ (* x (sin x)) (cos x))"
    @check |mut r: Runner<Math, ConstantFold>| {
        check_proof_exists(&mut r, rules(), "(* (d x x) (i (cos x) x))", "(sin x)");
    }
}

egg::test_fn! {
    math_prove_integ_part2, rules(),
    runner = Runner::default()
             .with_iter_limit(5),
    "(i (* (cos x) x) x)" => "(+ (* x (sin x)) (cos x))"
    @check |mut r: Runner<Math, ConstantFold>| {
        check_proof_exists(&mut r, rules(), "(i (* (cos x) x) x)", "(+ (* x (sin x)) (cos x))");
    }
}

egg::test_fn! {
    math_prove_integ_part2_harder_1, rules(),
    runner = Runner::default()
             .with_iter_limit(7),
    "(i (* (cos x) x) x)" => "(+ (* x (sin x)) (cos x))"
    @check |mut r: Runner<Math, ConstantFold>| {
        check_proof_exists(&mut r, rules(), "(* x (i (cos x) x))", "(* x (sin x))");
    }

}

//"(- (* x (i (cos x) x)) (i (* (d x x) (i (cos x) x)) x))"
egg::test_fn! {
    math_prove_integ_part2_harder, rules(),
    runner = Runner::default()
             .with_iter_limit(7),
    "(i (* (cos x) x) x)" => "(+ (* x (sin x)) (cos x))"
    @check |mut r: Runner<Math, ConstantFold>| {
        check_proof_exists(&mut r, rules(), "(i (* (cos x) x) x)", "(+ (* x (sin x)) (cos x))");
    }
}
