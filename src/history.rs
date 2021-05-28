use crate::util::{HashMap, HashSet};
use crate::{
    Analysis, Applications, EGraph, ENodeOrVar, Id, Language, PatternAst, RecExpr, Rewrite, Subst,
    Var,
};
use rpds::{HashTrieMap, HashTrieSet, List, Vector};
use std::collections::VecDeque;
use std::rc::Rc;
use symbolic_expressions::Sexp;

pub type Proof<L> = Vec<Rc<NodeExpr<L>>>;

// so that creating a new path with 1 added is O(log(n))
type SeenMemo<L> = HashTrieSet<(Rc<NodeExpr<L>>, Rc<NodeExpr<L>>)>;
type VarMemo<L> = Vector<Rc<NodeExpr<L>>>;
type ExprMemo<L> = HashTrieSet<Rc<NodeExpr<L>>>;
type ResultFailCache<L> = HashMap<(Rc<NodeExpr<L>>, Rc<NodeExpr<L>>), usize>;
type AgeRec<L> = HashMap<usize, (usize, Rc<NodeExpr<L>>)>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
enum RuleReference<L> {
    Congruence,
    Index(usize),
    Pattern((PatternAst<L>, PatternAst<L>, String)),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct RewriteConnection<L: Language> {
    pub index: usize,
    subst: Subst,
    pub is_direction_forward: bool,
    rule_ref: RuleReference<L>,
    age: usize,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct GraphNode<L: Language> {
    pub node: L,
    pub children: Vec<RewriteConnection<L>>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct NodeExpr<L: Language> {
    node: Option<L>, // sometimes we have a hole
    children: Vec<Rc<NodeExpr<L>>>,
    rule_ref: RuleReference<L>,
    is_direction_forward: bool,
    is_rewritten_forward: bool,
    is_rewritten_backwards: bool,
    var_reference: usize, // used to keep track of variable bindings, 0 means no reference
}

fn enode_to_string<L: Language>(node_ref: &L) -> String {
    let mut node: L = node_ref.clone();
    let mut strings = vec![];
    strings.push(format!("({}", node.display_op()));
    node.for_each_mut(|child| strings.push(format!(" {}", child)));
    strings.push(")".to_string());
    strings.concat()
}

fn unwrap_or_clone<L: Language>(node: Rc<NodeExpr<L>>) -> NodeExpr<L> {
    match Rc::try_unwrap(node) {
        Ok(n) => n,
        Err(original) => (*original).clone(),
    }
}

impl<L: Language> NodeExpr<L> {
    pub fn new(node: Option<L>, children: Vec<Rc<NodeExpr<L>>>) -> NodeExpr<L> {
        NodeExpr {
            node: node,
            children: children,
            rule_ref: RuleReference::Index(0),
            is_direction_forward: true,
            is_rewritten_forward: false,
            is_rewritten_backwards: false,
            var_reference: 0,
        }
    }

    pub fn to_strings<N: Analysis<L>>(
        rules: &[&Rewrite<L, N>],
        exprs: &Vec<Rc<NodeExpr<L>>>,
    ) -> Vec<String> {
        let mut res = vec![];
        for i in exprs {
            res.push(i.to_string());
            res.push(i.connection_string::<N>(rules));
        }
        res.pop();
        res
    }

    fn get_variable_refs(&self, acc: &mut Vec<usize>) {
        if self.var_reference != 0 {
            acc.push(self.var_reference);
        }
        self.children
            .iter()
            .for_each(|child| child.get_variable_refs(acc));
    }

    // TODO this function isn't sound, need a hash function and compare function instead
    pub fn alpha_normalize(&self) -> Rc<NodeExpr<L>> {
        let mut vars = vec![];
        self.get_variable_refs(&mut vars);
        vars.sort_unstable();
        vars.dedup();
        let mut map: HashMap<usize, usize> = Default::default();
        for (i, v) in vars.iter().enumerate() {
            map.insert(*v, i);
        }
        Rc::new(self.alpha_normalize_with(&map))
    }

    fn alpha_normalize_with(&self, map: &HashMap<usize, usize>) -> NodeExpr<L> {
        let mut head = self.clone();
        if self.var_reference != 0 {
            head.var_reference = *map.get(&head.var_reference).unwrap();
        }
        head.rule_ref = RuleReference::Index(0);
        head.is_rewritten_backwards = false;
        head.is_rewritten_forward = false;
        head.is_direction_forward = true;
        head.children = head
            .children
            .iter()
            .map(|child| {
                let c = child.alpha_normalize_with(map);
                Rc::new(c)
            })
            .collect();
        head
    }

    pub fn to_sexp(&self) -> Sexp {
        match &self.node {
            Some(node) => {
                let op = Sexp::String(node.display_op().to_string());
                let mut res = {
                    if self.children.len() > 0 {
                        let mut vec = vec![op];
                        for child in &self.children {
                            vec.push(child.to_sexp());
                        }
                        Sexp::List(vec)
                    } else {
                        op
                    }
                };

                if self.is_rewritten_forward {
                    res = Sexp::List(vec![Sexp::String("=>".to_string()), res]);
                }
                if self.is_rewritten_backwards {
                    res = Sexp::List(vec![Sexp::String("<=".to_string()), res]);
                }
                res
            }
            None => Sexp::String(
                "(variable-referencing ".to_string()
                    + &self.var_reference.to_string()
                    + &")".to_string(),
            ),
        }
    }

    pub fn to_string(&self) -> String {
        self.to_sexp().to_string()
    }

    pub fn connection_string<N: Analysis<L>>(&self, rules: &[&Rewrite<L, N>]) -> String {
        let reason = {
            match &self.rule_ref {
                RuleReference::Pattern((_l, _r, reason)) => reason,
                RuleReference::Index(rule_index) => &rules[*rule_index].name,
                RuleReference::Congruence => "congruence",
            }
        };

        if (self.is_direction_forward) {
            reason.to_owned() + &" =>"
        } else {
            "<= ".to_owned() + reason
        }
    }

    pub(crate) fn from_recexpr<N: Analysis<L>>(
        egraph: &mut EGraph<L, N>,
        expr: &RecExpr<L>,
    ) -> Self {
        let nodes = expr.as_ref();
        let mut nodeexprs: Vec<Rc<NodeExpr<L>>> = Vec::with_capacity(nodes.len());
        let mut new_ids = Vec::with_capacity(nodes.len());
        for node in nodes {
            let mut children: Vec<Rc<NodeExpr<L>>> = vec![];
            node.for_each(|i| children.push(nodeexprs[usize::from(i)].clone()));
            let graphnode = node.clone().map_children(|i| new_ids[usize::from(i)]);

            let expr = Rc::new(NodeExpr::new(Some(graphnode.clone()), children));
            nodeexprs.push(expr);
            new_ids.push(egraph.add(graphnode));
        }
        // unwrap last nodeexpr, the top node
        Rc::try_unwrap(nodeexprs.pop().unwrap()).unwrap()
    }

    pub(crate) fn from_pattern_ast<N: Analysis<L>>(
        egraph: &mut EGraph<L, N>,
        ast: &PatternAst<L>,
        subst: &Subst,
        substmap: Option<&HashMap<Var, Rc<NodeExpr<L>>>>, // optionally used to replace variables with nodeexpr
        var_memo: Option<VarMemo<L>>,                     // add this for variable bindings
    ) -> (Self, VarMemo<L>) {
        let mut dummy = Default::default();
        let use_memo = var_memo != None;
        let mut var_memo_unwrapped = var_memo.unwrap_or(dummy);
        let mut symbol_map: HashMap<&Var, usize> = Default::default();
        let nodes = ast.as_ref();
        let mut nodeexprs: Vec<Rc<NodeExpr<L>>> = Vec::with_capacity(nodes.len());
        let mut new_ids = Vec::with_capacity(nodes.len());
        for nodeorvar in nodes {
            match nodeorvar {
                ENodeOrVar::Var(v) => {
                    let mut added = false;
                    if let Some(map) = substmap {
                        if let Some(substitution) = map.get(v) {
                            nodeexprs.push(substitution.clone());
                            added = true;
                        }
                    }
                    if !added {
                        if use_memo {
                            let mut var_num = var_memo_unwrapped.len();
                            if let Some(n) = symbol_map.get(v) {
                                var_num = *n;
                            } else {
                                symbol_map.insert(v, var_num);
                                let mut new_placeholder = NodeExpr::new(None, vec![]);
                                new_placeholder.var_reference = var_num;
                                var_memo_unwrapped =
                                    var_memo_unwrapped.push_back(Rc::new(new_placeholder));
                            }

                            let mut newexpr = NodeExpr::new(None, vec![]);
                            newexpr.var_reference = var_num;
                            nodeexprs.push(Rc::new(newexpr));
                        } else {
                            nodeexprs.push(Rc::new(NodeExpr::new(None, vec![])));
                        }
                    }
                    // substs may have old ids
                    new_ids.push(egraph.find(subst[*v]));
                }
                ENodeOrVar::ENode(node) => {
                    let mut children: Vec<Rc<NodeExpr<L>>> = vec![];
                    node.for_each(|i| children.push(nodeexprs[usize::from(i)].clone()));
                    let graphnode = node.clone().map_children(|i| new_ids[usize::from(i)]);

                    let expr = Rc::new(NodeExpr::new(Some(graphnode.clone()), children));
                    nodeexprs.push(expr);
                    new_ids.push(egraph.add(graphnode));
                }
            }
        }

        // last nodeexpr, the top node
        (
            unwrap_or_clone(nodeexprs.pop().unwrap()),
            var_memo_unwrapped,
        )
    }

    fn make_subst(
        self: &Rc<NodeExpr<L>>,
        left: &PatternAst<L>,
        pos: Id,
        current: &mut HashMap<Var, Rc<NodeExpr<L>>>,
    ) {
        match &left[pos] {
            ENodeOrVar::Var(v) => {
                if current.get(v) == None {
                    current.insert(*v, self.clone());
                }
            }
            ENodeOrVar::ENode(node) => {
                let mut index = 0;
                node.for_each(|child| {
                    self.children[index]
                        .clone()
                        .make_subst(left, child, current);
                    index += 1;
                });
            }
        }
    }

    pub(crate) fn rewrite<N: Analysis<L>>(
        self: &Rc<NodeExpr<L>>,
        egraph: &mut EGraph<L, N>,
        left: &PatternAst<L>,
        right: &PatternAst<L>,
        subst: &Subst,
        var_memo: VarMemo<L>,
    ) -> (NodeExpr<L>, VarMemo<L>) {
        let mut graphsubst = Default::default();
        self.make_subst(left, Id::from(left.as_ref().len() - 1), &mut graphsubst);
        NodeExpr::from_pattern_ast::<N>(egraph, right, subst, Some(&graphsubst), Some(var_memo))
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct History<L: Language> {
    // connects nodes in the same eclass to each other, forming a tree for each eclass
    pub graph: Vec<GraphNode<L>>,
    memo: HashMap<Id, usize>,
    age_counter: usize,
}

impl<L: Language> Default for History<L> {
    fn default() -> Self {
        History::<L> {
            graph: Default::default(),
            memo: Default::default(),
            age_counter: 1,
        }
    }
}

impl<L: Language> History<L> {
    fn find_enode_in<N: Analysis<L>>(&self, enode: &L, class: Id, egraph: &EGraph<L, N>) -> usize {
        let mut seen: HashSet<usize> = Default::default();
        let mut todo: VecDeque<usize> = VecDeque::new();
        todo.push_back(*self.memo.get(&class).unwrap());

        while (true) {
            assert!(todo.len() > 0);
            let current = todo.pop_front().unwrap();
            let cnode = self.graph[current]
                .node
                .clone()
                .map_children(|id| egraph.find(id));
            if seen.contains(&current) {
                continue;
            }
            seen.insert(current);
            if &cnode == enode {
                return current;
            } else {
                for child in &self.graph[current].children {
                    todo.push_back(child.index);
                }
            }
        }
        assert!(false);
        return 0;
    }

    // from and to must be from different eclasses
    fn add_connection<N: Analysis<L>>(
        &mut self,
        from: L,
        to: L,
        fromid: Id,
        toid: Id,
        rule: RuleReference<L>,
        subst: Subst,
        egraph: &EGraph<L, N>,
    ) {
        let cfrom = from.clone().map_children(|id| egraph.find(id));
        let cto = to.clone().map_children(|id| egraph.find(id));
        let currentfrom = self.find_enode_in(&cfrom, fromid, egraph);
        let currentto = self.find_enode_in(&cto, toid, egraph);
        assert!(currentfrom != currentto);

        let fromr = RewriteConnection {
            index: currentto,
            subst: subst.clone(),
            is_direction_forward: true,
            rule_ref: rule.clone(),
            age: self.age_counter,
        };

        let tor = RewriteConnection {
            index: currentfrom,
            subst: subst.clone(),
            is_direction_forward: false,
            rule_ref: rule.clone(),
            age: self.age_counter,
        };

        self.graph[currentfrom].children.push(fromr);
        self.graph[currentto].children.push(tor);
        self.age_counter += 1;
    }

    pub fn union<N: Analysis<L>>(
        &mut self,
        from: L,
        to: L,
        fromid: Id,
        toid: Id,
        egraph: &EGraph<L, N>,
    ) {
        //println!("adding union {} and {}", fromid, toid);
        self.add_connection(
            from,
            to,
            fromid,
            toid,
            RuleReference::Congruence,
            Default::default(),
            egraph,
        );
    }

    pub fn add_new_node(&mut self, node: L, id: Id) {
        self.graph.push(GraphNode {
            node: node.clone(),
            children: Default::default(),
        });
        self.memo.insert(id, self.graph.len() - 1);
    }

    pub(crate) fn add_union_proof<N: Analysis<L>>(
        &mut self,
        egraph: &mut EGraph<L, N>,
        from: PatternAst<L>,
        to: PatternAst<L>,
        fromid: Id,
        toid: Id,
        subst: Subst,
        reason: String,
    ) {
        //println!("adding union proof {} and {}", fromid, toid);
        let from_node = NodeExpr::from_pattern_ast(egraph, &from, &subst, None, None).0;
        let to_node = NodeExpr::from_pattern_ast(egraph, &to, &subst, None, None).0;
        self.add_connection(
            from_node.node.as_ref().unwrap().clone(),
            to_node.node.unwrap(),
            fromid,
            toid,
            RuleReference::Pattern((from, to, reason)),
            subst,
            egraph,
        );
    }

    pub(crate) fn add_applications<N: Analysis<L>>(
        &mut self,
        egraph: &mut EGraph<L, N>,
        applications: Applications<L>,
        rule: usize,
    ) {
        for (from, to, subst, class, from_class) in izip!(
            applications.from_nodes,
            applications.to_nodes,
            applications.substs,
            applications.affected_classes,
            applications.from_classes
        ) {
            //println!("adding application {} and {}", from_class, class);
            let cfrom = from.clone().map_children(|child| egraph.find(child));
            let cto = to.clone().map_children(|child| egraph.find(child));
            self.add_connection(
                cfrom,
                cto,
                from_class,
                class,
                RuleReference::Index(rule),
                subst,
                egraph,
            );
        }
    }

    fn is_arbitrary<N: Analysis<L>>(
        rules: &[&Rewrite<L, N>],
        rule_ref: &RuleReference<L>,
        check_left: bool,
    ) -> bool {
        let mut pattern;
        match rule_ref {
            RuleReference::Index(i) => {
                if check_left {
                    pattern = rules[*i].searcher.get_ast().unwrap();
                } else {
                    pattern = rules[*i].applier.get_ast().unwrap();
                }
            }
            RuleReference::Pattern((s, a, _)) => {
                if check_left {
                    pattern = s;
                } else {
                    pattern = a;
                }
            }
            RuleReference::Congruence => return true,
        }
        if let ENodeOrVar::Var(_) = pattern.as_ref().last().unwrap() {
            return true;
        } else {
            return false;
        }
    }

    // updates memo to use cannonical references
    pub(crate) fn rebuild<N: Analysis<L>>(&mut self, egraph: &EGraph<L, N>) {
        for graphnode in self.graph.iter_mut() {
            graphnode.node = graphnode
                .node
                .clone()
                .map_children(|child| egraph.find(child));
        }
    }

    pub(crate) fn produce_proof<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left: &RecExpr<L>,
        right: &RecExpr<L>,
    ) -> Option<Proof<L>> {
        if egraph.add_expr(&left) != egraph.add_expr(&right) {
            return None;
        } else {
            let lg = Rc::new(NodeExpr::from_recexpr::<N>(egraph, left));
            let rg = Rc::new(NodeExpr::from_recexpr::<N>(egraph, right));
            let INITIAL_FUEL = 2;
            let MAX_FUEL = 20;
            let mut fuel = INITIAL_FUEL;
            while (fuel <= MAX_FUEL) {
                // push since 0 is a special value and represents no variable
                let var_memo = Vector::<Rc<NodeExpr<L>>>::new()
                    .push_back(Rc::new(NodeExpr::new(None, vec![])));
                let seen_memo: SeenMemo<L> = Default::default();
                // from an input to a fuel it failed for
                let mut result_fail_cache = Default::default();
                let r = self.find_proof_paths(
                    egraph,
                    rules,
                    lg.clone(),
                    rg.clone(),
                    var_memo,
                    seen_memo,
                    &mut result_fail_cache,
                    fuel,
                );
                fuel += 1;
                if r != None {
                    return Some(r.unwrap().0);
                }
            }
            return None;
        }
    }

    fn find_leaf_node(&self, start: usize) -> usize {
        let mut seen: HashSet<usize> = Default::default();
        let mut todo = start;
        seen.insert(todo);
        while (true) {
            let current = todo;
            if self.graph[current].children.len() == 1 {
                return current;
            } else {
                for child in &self.graph[current].children {
                    if !seen.contains(&child.index) {
                        todo = child.index;
                        break;
                    }
                }
                if (todo == current) {
                    assert!(self.graph[current].children.len() == 1);
                    return current;
                }
                seen.insert(current);
            }
        }
        assert!(false);
        return 0;
    }

    fn find_youngest_recursive<'a>(
        &'a self,
        current: usize,
        left: &Rc<NodeExpr<L>>,
        right: &Rc<NodeExpr<L>>,
        prev: &mut HashMap<usize, usize>,
        prevc: &mut HashMap<usize, &'a RewriteConnection<L>>,
        best_age: &mut usize,
        best_left: &mut usize,
        best_right: &mut usize,
        best_middle: &mut usize,
    ) -> (bool, bool, usize, usize, usize, usize) {
        let mut has_found_left: bool = false;
        let mut has_found_right: bool = false;
        let mut last_found_left_index: usize = 0;
        let mut last_found_right_index: usize = 0;
        let mut last_found_left_age: usize = usize::MAX;
        let mut last_found_right_age: usize = usize::MAX;

        if &self.graph[current].node == right.node.as_ref().unwrap()
            || &self.graph[current].node == left.node.as_ref().unwrap()
        {
            let isleft = &self.graph[current].node == left.node.as_ref().unwrap();
            if isleft {
                has_found_left = true;
                last_found_left_index = current;
                last_found_left_age = 0;
            } else {
                has_found_right = true;
                last_found_right_index = current;
                last_found_right_age = 0;
            }
        }

        for child in &self.graph[current].children {
            if prev.get(&child.index) == None {
                prev.insert(child.index, current);
                prevc.insert(child.index, &child);
                let (
                    child_left,
                    child_right,
                    child_left_index,
                    child_right_index,
                    mut child_left_age,
                    mut child_right_age,
                ) = self.find_youngest_recursive(
                    child.index,
                    left,
                    right,
                    prev,
                    prevc,
                    best_age,
                    best_left,
                    best_right,
                    best_middle,
                );
                child_left_age = usize::max(child_left_age, child.age);
                child_right_age = usize::max(child_right_age, child.age);
                if child_left {
                    if (child_left_age < last_found_left_age) || !has_found_left {
                        has_found_left = true;
                        last_found_left_age = child_left_age;
                        last_found_left_index = child_left_index;
                    }
                }
                if child_right {
                    if (child_right_age < last_found_right_age) || !has_found_right {
                        has_found_right = true;
                        last_found_right_age = child_right_age;
                        last_found_right_index = child_right_index;
                    }
                }
            }
        }

        if has_found_left && has_found_right {
            if usize::max(last_found_left_age, last_found_right_age) < *best_age {
                *best_age = usize::max(last_found_left_age, last_found_right_age);
                *best_left = last_found_left_index;
                *best_right = last_found_right_index;
                *best_middle = current;
            }
        }
        (
            has_found_left,
            has_found_right,
            last_found_left_index,
            last_found_right_index,
            last_found_left_age,
            last_found_right_age,
        )
    }

    fn matching_age_calculation<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        prog: &Rc<NodeExpr<L>>,
        representative: usize,
    ) -> AgeRec<L> {
        let mut ages: AgeRec<L> = Default::default();
        let mut child_ages: Vec<AgeRec<L>> = Default::default();
        for child in &prog.children {
            child_ages.push(self.rec_age_calculation(egraph, child));
        }
        // TODO don't unwrap node, what about variable ages
        let enode = prog.node.as_ref().unwrap();

        let mut seen: HashSet<usize> = Default::default();
        let mut todo: VecDeque<usize> = VecDeque::new();
        todo.push_back(representative);

        while (todo.len() > 0) {
            let current = todo.pop_front().unwrap();
            let cnode = self.graph[current]
                .node
                .clone()
                .map_children(|id| egraph.find(id));
            if seen.contains(&current) {
                continue;
            }
            seen.insert(current);
            if &cnode == enode {
                let mut age = 0;
                let mut iter = 0;
                let mut aprog = prog.clone();
                self.graph[current].node.for_each(|id| {
                    let cage = child_ages[iter].get(&usize::from(id)).unwrap();
                    if cage.0 > age {
                        age = cage.0;
                        aprog = cage.1.clone();
                    }
                    iter += 1;
                });
                ages.insert(current, (age, aprog));
            } else {
                for child in &self.graph[current].children {
                    todo.push_back(child.index);
                }
            }
        }
        ages
    }

    fn rec_age_calculation<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        prog: &Rc<NodeExpr<L>>
    ) -> AgeRec<L> {
        let class = egraph.lookup(prog.node.as_ref().unwrap().clone()).unwrap();
        let representative = *self.memo.get(&class).unwrap();
        // get all the ages from matching enodes
        let mut ages = self.matching_age_calculation(egraph, prog, representative);

        // propagate ages from matching enodes to eclass representatives
        let mut todo: VecDeque<usize> = VecDeque::new();
        for (key, age) in &ages {
            todo.push_back(*key);
        }

        // find nearest age until fixed point
        while(todo.len() > 0) {
            let current = todo.pop_front().unwrap();
            let age = ages.get(&current).unwrap().clone();
            for child in &self.graph[current].children {
                let mage = usize::max(age.0, child.age);
                let mprog = age.1.clone();
                if mage > ages.get(&child.index).unwrap_or(&(0, prog.clone())).0 {
                    ages.insert(child.index, (mage, mprog.clone()));
                    todo.push_back(child.index);   
                }
            }
        }

        ages
    }

    fn find_youngest_proof_path<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        left: &Rc<NodeExpr<L>>,
        right: &Rc<NodeExpr<L>>,
    ) -> (Vec<&RewriteConnection<L>>, Vec<&RewriteConnection<L>>) {
        if left.node.as_ref() == right.node.as_ref() {
            return (vec![], vec![]);
        }

        let mut prev: HashMap<usize, usize> = Default::default();
        let mut prevc: HashMap<usize, &RewriteConnection<L>> = Default::default();
        let class = egraph.lookup(left.node.as_ref().unwrap().clone()).unwrap();
        assert_eq!(
            class,
            egraph.lookup(right.node.as_ref().unwrap().clone()).unwrap()
        );
        self.find_enode_in(left.node.as_ref().unwrap(), class, egraph);
        self.find_enode_in(right.node.as_ref().unwrap(), class, egraph);
        let representative = self.find_leaf_node(*self.memo.get(&class).unwrap());
        prev.insert(representative, representative);
        let mut age = usize::MAX;
        let mut left_node = 0;
        let mut right_node = 0;
        let mut middle_node = 0;
        self.find_youngest_recursive(
            representative,
            left,
            right,
            &mut prev,
            &mut prevc,
            &mut age,
            &mut left_node,
            &mut right_node,
            &mut middle_node,
        );
        assert!(age < usize::MAX);

        let mut leftpath: Vec<&RewriteConnection<L>> = Default::default();
        let mut rightpath: Vec<&RewriteConnection<L>> = Default::default();

        let mut trail = left_node;
        while (true) {
            if (trail == middle_node) {
                break;
            }
            let p = prev[&trail];
            assert!(trail != p);
            leftpath.push(prevc.get(&trail).unwrap());
            trail = p;
        }
        trail = right_node;
        while (true) {
            if (trail == middle_node) {
                break;
            }
            let p = prev[&trail];
            assert!(trail != p);
            rightpath.push(prevc.get(&trail).unwrap());
            trail = p;
        }
        rightpath.reverse();
        return (leftpath, rightpath);
    }

    // find a sequence of rewrites between two enodes
    // fuel determines the maximum number of backtracks before giving up
    fn find_proof_paths<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left_input: Rc<NodeExpr<L>>,
        right_input: Rc<NodeExpr<L>>,
        var_memo: VarMemo<L>,
        seen_memo: SeenMemo<L>,
        result_fail_cache: &mut ResultFailCache<L>,
        fuel_in: usize,
    ) -> Option<(Vec<Rc<NodeExpr<L>>>, VarMemo<L>)> {
        // cost of this function
        let fuel = fuel_in;

        let mut current_var_memo = var_memo;
        let (left, new_memo_1) = History::<L>::get_from_var_memo(&left_input, current_var_memo);
        current_var_memo = new_memo_1;
        let (right, new_memo_2) = History::<L>::get_from_var_memo(&right_input, current_var_memo);
        current_var_memo = new_memo_2;

        println!("Prove {} and {}", left.to_string(), right.to_string());

        let seen_entry = (
            left.clone().alpha_normalize(),
            right.clone().alpha_normalize(),
        );

        if seen_memo.contains(&seen_entry) {
            panic!("Cycle detected");
            return None;
        }
        let new_seen_memo = seen_memo.insert(seen_entry.clone());

        // union them when they are both variables
        if (left.node == None && right.node == None) {
            let new_var_memo = History::<L>::var_memo_union(&left, &right, current_var_memo);
            return Some((vec![left.clone()], new_var_memo));
        }

        // empty proof when one of them is a hole
        if left.node == None {
            if left.var_reference > 0 {
                if current_var_memo.get(left.var_reference).unwrap().node == None {
                    let new_var_memo = current_var_memo
                        .set(left.var_reference, right.clone())
                        .unwrap();
                    return Some((vec![right.clone()], new_var_memo));
                }
            } else {
                return Some((vec![right.clone()], current_var_memo));
            }
        } else if right.node == None {
            if right.var_reference > 0 {
                if current_var_memo.get(right.var_reference).unwrap().node == None {
                    let new_var_memo = current_var_memo
                        .set(right.var_reference, left.clone())
                        .unwrap();
                    return Some((vec![left.clone()], new_var_memo));
                }
            } else {
                return Some((vec![left.clone()], current_var_memo));
            }
        }

        assert_eq!(
            egraph.lookup(left.node.as_ref().unwrap().clone()),
            egraph.lookup(right.node.as_ref().unwrap().clone())
        );

        let (leftpath, rightpath) = self.find_youngest_proof_path(egraph, &left, &right);
        let leftsize = leftpath.len();
        let rightsize = rightpath.len();
        let mut proof = vec![left.clone()];
        for i in 0..(leftsize + rightsize) {
            let mut connection;
            let mut is_backwards = false;
            if i < leftsize {
                connection = leftpath[i];
                is_backwards = true;
            } else {
                connection = rightpath[i - leftsize];
            }
            let recent = proof.pop().unwrap();
            if let Some((subproof, vmemo)) = self.prove_one_step(
                egraph,
                rules,
                recent,
                connection,
                current_var_memo,
                new_seen_memo.clone(),
                result_fail_cache,
                fuel,
                is_backwards,
            ) {
                current_var_memo = vmemo;
                proof.extend(subproof);
            } else {
                panic!("failed to find subproof");
                return None;
            }
        }

        if proof[proof.len() - 1].node != right.node {
            let latest = proof.pop().unwrap();
            let rest_of_proof = self.find_proof_paths(
                egraph,
                rules,
                latest,
                right.clone(),
                current_var_memo.clone(),
                new_seen_memo.clone(),
                result_fail_cache,
                fuel,
            );
            if let Some((subproof, vmemo)) = rest_of_proof {
                current_var_memo = vmemo;
                proof.extend(subproof);
            } else {
                return None;
            }
        } else {
            let (success, vmemo) = self.prove_children_equal(
                egraph,
                rules,
                right.clone(),
                &mut proof,
                current_var_memo.clone(),
                new_seen_memo.clone(),
                result_fail_cache,
                fuel_in,
            );
            if success {
                current_var_memo = vmemo;
            } else {
                panic!("Failed to prove children equal");
                return None;
            }
        }

        Some((proof, current_var_memo))
    }

    fn get_from_var_memo(
        node: &Rc<NodeExpr<L>>,
        var_memo_in: VarMemo<L>,
    ) -> (Rc<NodeExpr<L>>, VarMemo<L>) {
        let mut var_memo = var_memo_in;
        let mut current = node.clone();
        let mut var_ref = 0;
        while current.var_reference != var_ref && current.node == None {
            var_ref = current.var_reference;
            current = var_memo.get(current.var_reference).unwrap().clone();
        }

        if node.var_reference != 0 {
            if node.var_reference != var_ref {
                let mut replacement = (**var_memo.get(node.var_reference).unwrap()).clone();
                replacement.var_reference = var_ref;
                var_memo = var_memo
                    .set(node.var_reference, Rc::new(replacement))
                    .unwrap();
            }
        }
        return (current, var_memo);
    }

    fn var_memo_union(
        left: &Rc<NodeExpr<L>>,
        right: &Rc<NodeExpr<L>>,
        var_memo: VarMemo<L>,
    ) -> VarMemo<L> {
        var_memo.set(right.var_reference, left.clone()).unwrap()
    }

    fn prove_one_step<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left: Rc<NodeExpr<L>>,
        connection: &RewriteConnection<L>,
        var_memo: Vector<Rc<NodeExpr<L>>>,
        seen_memo: SeenMemo<L>,
        result_fail_cache: &mut ResultFailCache<L>,
        fuel: usize,
        is_backwards: bool,
    ) -> Option<(Vec<Rc<NodeExpr<L>>>, Vector<Rc<NodeExpr<L>>>)> {
        // returns a new var_memo
        let mut current_var_memo = var_memo;
        let varpat = "?a".parse::<PatternAst<L>>().unwrap();

        let mut sast = match &connection.rule_ref {
            RuleReference::Index(i) => rules[*i]
                .searcher
                .get_ast()
                .unwrap_or_else(|| panic!("Applier must implement get_ast function")),
            RuleReference::Pattern((left, _right, _reaon)) => &left,
            RuleReference::Congruence => return Some((vec![left], current_var_memo)),
        };

        let mut rast = match &connection.rule_ref {
            RuleReference::Index(i) => rules[*i]
                .applier
                .get_ast()
                .unwrap_or_else(|| panic!("Applier must implement get_ast function")),
            RuleReference::Pattern((_left, right, _reaon)) => right,
            RuleReference::Congruence => return Some((vec![left], current_var_memo)),
        };

        let mut direction = connection.is_direction_forward;
        if is_backwards {
            direction = !direction;
        }
        if !direction {
            std::mem::swap(&mut sast, &mut rast);
        }

        println!("Rule {} to {}", sast, rast);

        let (search_pattern, first_var_memo) = NodeExpr::from_pattern_ast::<N>(
            egraph,
            sast,
            &connection.subst,
            None,
            Some(current_var_memo),
        );
        current_var_memo = first_var_memo;

        let maybe_subproof = self.find_proof_paths(
            egraph,
            rules,
            left.clone(),
            Rc::new(search_pattern),
            current_var_memo,
            seen_memo.clone(),
            result_fail_cache,
            fuel,
        );
        if maybe_subproof == None {
            return None;
        }
        let unwrapped_subproof = maybe_subproof.unwrap();
        let mut proof = unwrapped_subproof.0;
        current_var_memo = unwrapped_subproof.1;

        let latest = proof.pop().unwrap();
        let (mut next, third_var_memo) =
            latest.rewrite::<N>(egraph, sast, rast, &connection.subst, current_var_memo);
        current_var_memo = third_var_memo;
        let mut newlink = unwrap_or_clone(latest);
        newlink.rule_ref = connection.rule_ref.clone();
        newlink.is_direction_forward = direction;
        if direction {
            newlink.is_rewritten_forward = true;
            next.is_rewritten_backwards = false;
        } else {
            newlink.is_rewritten_forward = false;
            next.is_rewritten_backwards = true;
        }
        proof.push(Rc::new(newlink));
        proof.push(Rc::new(next));
        Some((proof, current_var_memo))
    }

    fn prove_children_equal<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        right: Rc<NodeExpr<L>>,
        proof: &mut Vec<Rc<NodeExpr<L>>>,
        var_memo: Vector<Rc<NodeExpr<L>>>,
        seen_memo: SeenMemo<L>,
        result_fail_cache: &mut ResultFailCache<L>,
        fuel: usize,
    ) -> (bool, VarMemo<L>) {
        let left = proof[proof.len() - 1].clone();
        if left.children.len() != right.children.len() {
            panic!(
                "Found equal enodes but different number of children: {} and {}",
                left.to_string(),
                right.to_string()
            );
        }
        let mut current_var_memo = var_memo;
        for i in 0..left.children.len() {
            let lchild = left.children[i].clone();
            let rchild = right.children[i].clone();
            let proof_equal_maybe = self.find_proof_paths(
                egraph,
                rules,
                lchild,
                rchild,
                current_var_memo,
                seen_memo.clone(),
                result_fail_cache,
                fuel,
            );
            if proof_equal_maybe == None {
                return (false, Default::default());
            }
            let (proof_equal, new_var_memo) = proof_equal_maybe.unwrap();
            current_var_memo = new_var_memo;
            let mut latest = proof.pop().unwrap();
            for j in 0..proof_equal.len() {
                let mut newlink = unwrap_or_clone(latest);
                newlink.children[i] = proof_equal[j].clone();
                newlink.rule_ref = proof_equal[j].rule_ref.clone();
                newlink.is_direction_forward = proof_equal[j].is_direction_forward;
                if j != 0 {
                    newlink.is_rewritten_forward = false;
                    newlink.is_rewritten_backwards = false;
                }
                proof.push(Rc::new(newlink));
                latest = proof[proof.len() - 1].clone()
            }
        }
        (true, current_var_memo)
    }
}
