use crate::util::{HashMap, HashSet};
use crate::{
    Analysis, Applications, EGraph, ENodeOrVar, Id, Language, PatternAst, RecExpr, Rewrite, Subst,
    Var,
};

use log::debug;

use rpds::HashTrieSet;
use std::collections::VecDeque;
use std::rc::Rc;
use symbolic_expressions::Sexp;

pub type Proof<L> = Vec<Rc<NodeExpr<L>>>;

type SeenMemo<L> = HashTrieSet<(Rc<NodeExpr<L>>, Rc<NodeExpr<L>>)>;
// from node to (age, start-pointer, nodeexpr, classpointer)
type AgeRec<L> = HashMap<usize, (usize, usize, Rc<NodeExpr<L>>, usize)>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
enum RuleReference<L> {
    Congruence(L, L), // the nodes before cannonicalization
    Index(usize),
    Pattern((PatternAst<L>, PatternAst<L>, String)),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct RewriteConnection<L: Language> {
    pub index: usize,
    pub prev: usize,
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
    node: L, // sometimes we have a hole
    children: Vec<Rc<NodeExpr<L>>>,
    rule_ref: RuleReference<L>,
    is_direction_forward: bool,
    is_rewritten_forward: bool,
    is_rewritten_backwards: bool,
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

fn clone_rc<L: Language>(node: &Rc<NodeExpr<L>>) -> NodeExpr<L> {
    (**node).clone()
}

impl<L: Language> NodeExpr<L> {
    pub fn new(node: L, children: Vec<Rc<NodeExpr<L>>>) -> NodeExpr<L> {
        NodeExpr {
            node: node,
            children: children,
            rule_ref: RuleReference::Index(0),
            is_direction_forward: true,
            is_rewritten_forward: false,
            is_rewritten_backwards: false,
        }
    }

    pub fn ast_size(&self) -> usize {
        let mut res = 1;
        for child in &self.children {
            res += child.ast_size()
        }
        res
    }

    pub fn proof_to_string<N: Analysis<L>>(
        rules: &[&Rewrite<L, N>],
        exprs: &Vec<Rc<NodeExpr<L>>>,
    ) -> String {
        let strings = NodeExpr::to_strings(rules, exprs);
        strings.join("\n")
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

    pub fn alpha_normalize(&self) -> Rc<NodeExpr<L>> {
        Rc::new(self.remove_rewrite_dirs())
    }

    pub fn equal_to(&self, other: &Rc<NodeExpr<L>>) -> bool {
        if self.node != other.node || self.children.len() != other.children.len() {
            return false;
        }
        let mut counter = 0;
        for child in &self.children {
            if !child.equal_to(&other.children[counter]) {
                return false;
            }
            counter += 1;
        }
        return true;
    }

    fn deep_copy(&self) -> NodeExpr<L> {
        let mut head = self.clone();
        head.is_rewritten_backwards = false;
        head.is_rewritten_forward = false;
        head.children = head
            .children
            .iter()
            .map(|child| Rc::new(child.deep_copy()))
            .collect();
        head
    }

    pub fn count_forward(&self) -> usize {
        self.count_specified(true)
    }

    pub fn count_backwards(&self) -> usize {
        self.count_specified(false)
    }

    fn count_specified(&self, forward: bool) -> usize {
        let mut count = 0;
        if forward && self.is_rewritten_forward {
            count += 1;
        } else if !forward && self.is_rewritten_backwards {
            count += 1;
        }

        for child in &self.children {
            count += child.count_specified(forward);
        }
        count
    }

    pub fn remove_rewrite_dirs(&self) -> NodeExpr<L> {
        let mut head = self.clone();
        head.is_rewritten_backwards = false;
        head.is_rewritten_forward = false;
        head.rule_ref = RuleReference::Index(0);
        head.children = head
            .children
            .iter()
            .map(|child| {
                let c = child.remove_rewrite_dirs();
                Rc::new(c)
            })
            .collect();
        head
    }

    pub fn combine_dirs(&self, other: &Rc<NodeExpr<L>>) -> NodeExpr<L> {
        let mut head = self.clone();
        head.is_rewritten_backwards = head.is_rewritten_backwards || other.is_rewritten_backwards;
        head.is_rewritten_forward = head.is_rewritten_forward || other.is_rewritten_forward;
        assert!(other.children.len() == self.children.len());
        let mut counter = 0;

        head.children = head
            .children
            .iter()
            .map(|child| {
                let c = child.combine_dirs(&other.children[counter]);
                counter += 1;
                Rc::new(c)
            })
            .collect();
        head
    }

    pub fn reverse_rewrite_dir(&self) -> NodeExpr<L> {
        let mut head = self.clone();
        head.is_rewritten_backwards = false;
        head.is_rewritten_forward = false;

        if self.is_rewritten_backwards {
            head.is_rewritten_forward = true;
        }
        if self.is_rewritten_forward {
            head.is_rewritten_backwards = true;
        }

        head.children = head
            .children
            .iter()
            .map(|child| {
                let c = child.reverse_rewrite_dir();
                Rc::new(c)
            })
            .collect();
        head
    }

    pub fn to_sexp(&self) -> Sexp {
        let op = Sexp::String(self.node.display_op().to_string());
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

    pub fn to_string(&self) -> String {
        self.to_sexp().to_string()
    }

    pub fn connection_string<N: Analysis<L>>(&self, rules: &[&Rewrite<L, N>]) -> String {
        let reason = {
            match &self.rule_ref {
                RuleReference::Pattern((_l, _r, reason)) => reason,
                RuleReference::Index(rule_index) => &rules[*rule_index].name,
                RuleReference::Congruence(_l, _r) => "congruence",
            }
        };

        if self.is_direction_forward {
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

            let expr = Rc::new(NodeExpr::new(graphnode.clone(), children));
            nodeexprs.push(expr);
            new_ids.push(egraph.add(graphnode));
        }
        // unwrap last nodeexpr, the top node
        Rc::try_unwrap(nodeexprs.pop().unwrap()).unwrap()
    }

    pub(crate) fn from_pattern_ast<N: Analysis<L>>(
        history: &History<L>,
        egraph: &mut EGraph<L, N>,
        ast: &PatternAst<L>,
        subst: Option<&Subst>, // used in proof checking, we have a full expression to rewrite
        substmap: Option<&HashMap<Var, Rc<NodeExpr<L>>>>, // optionally used to replace variables with nodeexpr
    ) -> Self {
        let nodes = ast.as_ref();
        let mut nodeexprs: Vec<Rc<NodeExpr<L>>> = Vec::with_capacity(nodes.len());
        let mut new_ids = Vec::with_capacity(nodes.len());
        for nodeorvar in nodes {
            match nodeorvar {
                ENodeOrVar::Var(v) => {
                    let mut added = false;
                    if let Some(map) = substmap {
                        if let Some(substitution) = map.get(v) {
                            nodeexprs.push(Rc::new(substitution.deep_copy()));
                            added = true;
                        }
                    }
                    if !added {
                        nodeexprs.push(Rc::new(
                            history.build_term_age_0(egraph, usize::from(subst.unwrap()[*v])),
                        ));
                    }
                    // substs may have old ids
                    if let Some(s) = subst {
                        new_ids.push(egraph.find(s[*v]));
                    } else {
                        // then we must already have an enode
                        let node = &nodeexprs.last().unwrap().node;
                        new_ids.push(egraph.lookup(node.clone()).unwrap());
                    }
                }
                ENodeOrVar::ENode(node) => {
                    let mut children: Vec<Rc<NodeExpr<L>>> = vec![];
                    node.for_each(|i| children.push(nodeexprs[usize::from(i)].clone()));
                    let graphnode = node.clone().map_children(|i| new_ids[usize::from(i)]);

                    let expr = Rc::new(NodeExpr::new(graphnode.clone(), children));
                    nodeexprs.push(expr);
                    new_ids.push(egraph.add(graphnode));
                }
            }
        }

        // last nodeexpr, the top node
        unwrap_or_clone(nodeexprs.pop().unwrap())
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
        history: &History<L>,
        egraph: &mut EGraph<L, N>,
        left: &PatternAst<L>,
        right: &PatternAst<L>,
        subst: Option<&Subst>,
    ) -> NodeExpr<L> {
        let mut graphsubst = Default::default();
        self.make_subst(left, Id::from(left.as_ref().len() - 1), &mut graphsubst);
        NodeExpr::from_pattern_ast::<N>(history, egraph, right, subst, Some(&graphsubst))
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct History<L: Language> {
    // connects nodes in the same eclass to each other, forming a tree for each eclass
    pub graph: Vec<GraphNode<L>>,
    memo: HashMap<Id, usize>,
    pub age_counter: usize,
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

        loop {
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
        let age = self.age_counter;
        self.age_counter += 1;

        let cfrom = from.clone().map_children(|id| egraph.find(id));
        let cto = to.clone().map_children(|id| egraph.find(id));
        let currentfrom = self.find_enode_in(&cfrom, fromid, egraph);
        let currentto = self.find_enode_in(&cto, toid, egraph);
        assert!(currentfrom != currentto);

        let fromr = RewriteConnection {
            index: currentto,
            prev: currentfrom,
            subst: subst.clone(),
            is_direction_forward: true,
            rule_ref: rule.clone(),
            age: age,
        };

        let tor = RewriteConnection {
            index: currentfrom,
            prev: currentto,
            subst: subst.clone(),
            is_direction_forward: false,
            rule_ref: rule.clone(),
            age: age,
        };

        self.graph[currentfrom].children.push(fromr);
        self.graph[currentto].children.push(tor);
    }

    pub fn union<N: Analysis<L>>(
        &mut self,
        from: L,
        to: L,
        fromid: Id,
        toid: Id,
        egraph: &EGraph<L, N>,
    ) {
        assert!(from != to);
        self.add_connection(
            from.clone(),
            to.clone(),
            fromid,
            toid,
            RuleReference::Congruence(from, to),
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
        let from_node = NodeExpr::from_pattern_ast(self, egraph, &from, Some(&subst), None);
        let to_node = NodeExpr::from_pattern_ast(self, egraph, &to, Some(&subst), None);

        self.add_connection(
            from_node.node.clone(),
            to_node.node.clone(),
            fromid,
            toid,
            RuleReference::Pattern((from, to, reason)),
            subst,
            egraph,
        );
    }

    pub(crate) fn add_union<N: Analysis<L>>(
        &mut self,
        egraph: &mut EGraph<L, N>,
        from: L,
        to: L,
        subst: Subst,
        class: Id,
        from_class: Id,
        rule: usize,
    ) {
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

    // updates memo to use cannonical references
    /*
    pub(crate) fn rebuild<N: Analysis<L>>(&mut self, egraph: &EGraph<L, N>) {
        for graphnode in self.graph.iter_mut() {
            graphnode.node = graphnode
                .node
                .clone()
                .map_children(|child| egraph.find(child));
        }
    }*/

    pub(crate) fn produce_proof<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left: &RecExpr<L>,
        right: &RecExpr<L>,
    ) -> Option<Proof<L>> {
        debug!("Produce proof!");
        if egraph.add_expr(&left) != egraph.add_expr(&right) {
            return None;
        } else {
            let lg = Rc::new(NodeExpr::from_recexpr::<N>(egraph, left));
            let rg = Rc::new(NodeExpr::from_recexpr::<N>(egraph, right));
            // push since 0 is a special value and represents no variable
            let seen_memo: SeenMemo<L> = Default::default();
            // from an input to a fuel it failed for
            let proof = self.find_proof_paths(egraph, rules, lg.clone(), rg.clone(), seen_memo);
            assert!(self.check_proof(egraph, rules, &proof));
            return Some(proof);
        }
    }

    fn check_proof<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        proof: &Proof<L>,
    ) -> bool {
        for i in 0..proof.len() {
            let current = &proof[i];
            let mut num_forward = 0;
            let mut num_backward = 0;

            if i > 0 {
                if !proof[i - 1].is_direction_forward {
                    num_backward = 1;
                }
            }

            if i < proof.len() - 1 {
                if proof[i].is_direction_forward {
                    num_forward = 1;
                }
            }

            if current.count_forward() != num_forward {
                println!("{}", NodeExpr::<L>::proof_to_string(rules, proof));
                println!(
                    "Count forward bad at {}! Expected {} got {}",
                    proof[i].to_string(),
                    num_forward,
                    current.count_forward()
                );
                return false;
            } else if current.count_backwards() != num_backward {
                println!("{}", NodeExpr::<L>::proof_to_string(rules, proof));
                println!("Count backward bad at {}!", proof[i].to_string());
                return false;
            }
        }

        for i in 0..proof.len() - 1 {
            let connection = &proof[i];
            let next = &proof[i + 1];

            let mut sast = match &connection.rule_ref {
                RuleReference::Index(i) => rules[*i]
                    .searcher
                    .get_ast()
                    .unwrap_or_else(|| panic!("Applier must implement get_ast function")),
                RuleReference::Pattern((left, _right, _reaon)) => &left,
                RuleReference::Congruence(_l, _r) => return false,
            };

            let mut rast = match &connection.rule_ref {
                RuleReference::Index(i) => rules[*i]
                    .applier
                    .get_ast()
                    .unwrap_or_else(|| panic!("Applier must implement get_ast function")),
                RuleReference::Pattern((_left, right, _reaon)) => right,
                RuleReference::Congruence(_l, _r) => return false,
            };

            let rewritten;
            let mut other = connection.clone();
            if connection.is_direction_forward {
                rewritten =
                    Rc::new(self.rewrite_part(egraph, connection.clone(), sast, rast, true));
                other = next.clone();
            } else {
                rewritten = Rc::new(self.rewrite_part(egraph, next.clone(), sast, rast, false));
            }
            if !rewritten.equal_to(&other) {
                println!("{}", NodeExpr::<L>::proof_to_string(rules, proof));
                println!(
                    "Proof check failed {} and {}",
                    rewritten.to_string(),
                    other.to_string()
                );
                return false;
            }
        }

        true
    }

    fn find_leaf_node(&self, start: usize) -> usize {
        let mut seen: HashSet<usize> = Default::default();
        let mut todo = start;
        seen.insert(todo);
        loop {
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
                if todo == current {
                    assert!(self.graph[current].children.len() <= 1);
                    return current;
                }
                seen.insert(current);
            }
        }
    }

    fn prove_to_index<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left_in: Rc<NodeExpr<L>>,
        seen_memo: SeenMemo<L>,
        target_index: usize,
    ) -> Proof<L> {
        let left = Rc::new(left_in.remove_rewrite_dirs());
        let mut proof = vec![left];

        loop {
            if &proof[proof.len() - 1].node
                == &self.graph[target_index]
                    .node
                    .clone()
                    .map_children(|id| egraph.find(id))
            {
                return proof;
            }
            let current = proof.pop().unwrap();
            let ages = self.rec_age_calculation(egraph, &current, target_index);
            let including = ages[&target_index].clone();
            let mut subproof = self.take_path_including(
                egraph,
                rules,
                current.clone(),
                seen_memo.clone(),
                including,
                true,
                true,
            );
            subproof[0] = Rc::new(subproof[0].combine_dirs(&current));
            proof.extend(subproof);
        }
    }

    fn find_youngest_recursive<'a, N: Analysis<L>>(
        &'a self,
        current: usize,
        egraph: &mut EGraph<L, N>,
        left: &Rc<NodeExpr<L>>,
        right: &Rc<NodeExpr<L>>,
        left_ages: &AgeRec<L>,
        right_ages: &AgeRec<L>,
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

        let cnode = self.graph[current]
            .node
            .clone()
            .map_children(|id| egraph.find(id));
        let ornode = right.node.clone().map_children(|id| egraph.find(id));
        let olnode = left.node.clone().map_children(|id| egraph.find(id));

        if cnode == ornode {
            has_found_right = true;
            last_found_right_index = current;
            last_found_right_age = right_ages.get(&current).unwrap().0;
        }
        if cnode == olnode {
            has_found_left = true;
            last_found_left_index = current;
            last_found_left_age = left_ages.get(&current).unwrap().0;
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
                    egraph,
                    left,
                    right,
                    left_ages,
                    right_ages,
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
        let mut index = 0;
        prog.node.for_each(|child_id| {
            let child = &prog.children[index];
            index += 1;
            child_ages.push(self.rec_age_calculation(egraph, child, usize::from(child_id)));
        });
        let enode = prog.node.clone();

        let mut seen: HashSet<usize> = Default::default();
        let mut todo: VecDeque<usize> = VecDeque::new();
        todo.push_back(representative);

        while todo.len() > 0 {
            let current = todo.pop_front().unwrap();
            let cnode = self.graph[current]
                .node
                .clone()
                .map_children(|id| egraph.find(id));
            if seen.contains(&current) {
                continue;
            }
            seen.insert(current);
            let mut node_match = false;
            let enode_update = enode.clone().map_children(|id| egraph.find(id));
            if enode_update == cnode {
                node_match = true;
            }

            if node_match {
                let mut age = 0;
                let mut iter = 0;
                let mut pointer = current;
                let mut aprog = prog.clone();
                self.graph[current].node.for_each(|id| {
                    let cage = child_ages[iter].get(&usize::from(id)).unwrap();

                    if cage.0 > age {
                        age = cage.0;
                        pointer = cage.1;
                        aprog = cage.2.clone();
                    }
                    iter += 1;
                });
                ages.insert(current, (age, pointer, aprog, current));
            }

            for child in &self.graph[current].children {
                todo.push_back(child.index);
            }
        }
        ages
    }

    fn print_eclass<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        prog: &Rc<NodeExpr<L>>,
        representative: usize,
    ) {
        let mut todo: VecDeque<usize> = VecDeque::new();
        todo.push_back(representative);
        let mut seen: HashSet<usize> = Default::default();
        seen.insert(representative);

        println!("Prog enode {}", enode_to_string(&prog.node));

        while todo.len() > 0 {
            let current = todo.pop_front().unwrap();
            println!(
                "Current {}, enode {}, uncann {}",
                current,
                enode_to_string(
                    &self.graph[current]
                        .node
                        .clone()
                        .map_children(|child| egraph.find(child))
                ),
                enode_to_string(&self.graph[current].node)
            );

            for child in &self.graph[current].children {
                if !seen.contains(&child.index) {
                    todo.push_front(child.index);
                    seen.insert(child.index);
                    println!("Connects {}, age {}", child.index, child.age);
                }
            }
        }
    }

    fn rec_age_calculation<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        prog: &Rc<NodeExpr<L>>,
        representative: usize,
    ) -> AgeRec<L> {
        // get all the ages from matching enodes
        let mut ages = self.matching_age_calculation(egraph, prog, representative);

        // propagate ages from matching enodes to eclass representatives
        let mut todo: VecDeque<usize> = VecDeque::new();
        for (key, age) in &ages {
            todo.push_back(*key);
        }

        // find nearest age until fixed point
        while todo.len() > 0 {
            let current = todo.pop_front().unwrap();
            let age = ages.get(&current).unwrap().clone();
            for child in &self.graph[current].children {
                let mut mage = age.0;
                let mut pointer = age.1;
                let mut mprog = age.2.clone();
                let classpointer = age.3;
                // if the age is from this eclass, we point to represented enode

                if child.age > mage {
                    mage = child.age;
                    pointer = classpointer;
                    mprog = prog.clone();
                }

                let temp = (usize::MAX, 0, prog.clone(), 0);
                let current_age = ages.get(&child.index).unwrap_or(&temp);
                if mage < current_age.0 {
                    ages.insert(child.index, (mage, pointer, mprog, classpointer));
                    todo.push_back(child.index);
                }
            }
        }

        ages
    }

    fn reverse_proof<N: Analysis<L>>(
        &self,
        mut proof: Vec<Rc<NodeExpr<L>>>,
    ) -> Vec<Rc<NodeExpr<L>>> {
        proof.reverse();

        for i in 0..(proof.len()) {
            let mut replacement = clone_rc(&proof[i]);
            if i != proof.len() - 1 {
                replacement.rule_ref = proof[i + 1].rule_ref.clone();
                replacement.is_direction_forward = !proof[i + 1].is_direction_forward;
            }

            replacement = replacement.reverse_rewrite_dir();

            proof[i] = Rc::new(replacement);
        }

        proof
    }

    fn take_path_including<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left: Rc<NodeExpr<L>>,
        current_seen_memo: SeenMemo<L>,
        including: (usize, usize, Rc<NodeExpr<L>>, usize),
        is_by_age: bool, // otherwise, including.0 is an index
        should_decrease_age: bool,
    ) -> Proof<L> {
        // use pointer equality- we want the specific sub-expression
        if &*including.2 as *const NodeExpr<L> == &*left as *const NodeExpr<L> {
            if is_by_age {
                assert!(including.0 > 0);
            }
            let mut prev: HashMap<usize, usize> = Default::default();
            let mut prevc: HashMap<usize, &RewriteConnection<L>> = Default::default();
            let mut todo: VecDeque<usize> = VecDeque::new();

            debug!("found including path: {}", left.to_string());
            todo.push_back(including.1);
            let mut end = 0;
            let mut found = false;
            /*
            for connection in &self.graph[including.1].children {
                match &connection.rule_ref {
                    RuleReference::Pattern((searcher, applier, _)) => {
                        debug!("Rule found: {}, {}", searcher, applier);
                    }
                    RuleReference::Index(index) => {
                        debug!("Rule index found: {}, {}", rules[*index].searcher.get_ast().unwrap(), rules[*index].applier.get_ast().unwrap());
                    }
                    _ => {}
                }
            }*/

            assert!(
                self.graph[including.1]
                    .node
                    .clone()
                    .map_children(|id| egraph.find(id))
                    == left.node.clone()
            );

            while todo.len() > 0 {
                let current = todo.pop_front().unwrap();
                for connection in &self.graph[current].children {
                    let child = connection.index;

                    if (is_by_age && (connection.age == including.0))
                        || ((!is_by_age) && (child == including.0))
                    {
                        // we found our final connection
                        prev.insert(child, current);
                        prevc.insert(child, &connection);
                        end = child;
                        found = true;
                        break;
                    }

                    if prev.get(&child) == None {
                        prev.insert(child, current);
                        prevc.insert(child, &connection);
                        todo.push_back(child);
                    }
                }
                if found {
                    break;
                }
            }
            // make sure we did find our included node
            assert!(found);
            //assert!(&self.graph[end].node.clone().map_children(|id| egraph.find(id)) != left.node);

            let mut path: Vec<&RewriteConnection<L>> = Default::default();

            let mut trail = end;
            loop {
                if (trail == including.1) {
                    break;
                }
                let p = prev[&trail];
                assert!(trail != p);
                path.push(prevc.get(&trail).unwrap());
                trail = p;
            }
            debug!("end index {}", end);
            debug!("start index {}", including.1);
            debug!(
                "end enode {}",
                enode_to_string(
                    &self.graph[end]
                        .node
                        .clone()
                        .map_children(|id| egraph.find(id))
                )
            );
            debug!("start enode {}", enode_to_string(&left.node));
            debug!("applying found path, size {}", path.len());

            for connection in path.iter().rev() {
                match &connection.rule_ref {
                    RuleReference::Pattern((searcher, applier, _)) => {
                        debug!(
                            "Rule found: {}, {}, {}",
                            searcher, applier, connection.is_direction_forward
                        );
                    }
                    RuleReference::Index(index) => {
                        debug!(
                            "Rule index found: {}, {}, {}",
                            rules[*index].searcher.get_ast().unwrap(),
                            rules[*index].applier.get_ast().unwrap(),
                            connection.is_direction_forward
                        );
                    }
                    RuleReference::Congruence(l, r) => {
                        debug!(
                            "Congruence found from {} to {}",
                            enode_to_string(l),
                            enode_to_string(r)
                        );
                    }
                }
            }
            path.reverse();
            let resulting_proof = self.apply_path(
                egraph,
                rules,
                left,
                true,
                current_seen_memo.clone(),
                (path, vec![]),
            );

            if should_decrease_age {
                let new_age =
                    self.rec_age_calculation(egraph, resulting_proof.last().unwrap(), end);
                debug!("Resulting age after path {}", new_age.get(&end).unwrap().0);

                if new_age.get(&end).unwrap().0 >= including.0 {
                    println!("Age didn't decrease!");
                    println!(
                        "Age before {} age now {}",
                        including.0,
                        new_age.get(&end).unwrap().0
                    );
                    println!(
                        "Last program {}",
                        resulting_proof.last().unwrap().clone().to_string()
                    );
                    println!("Age program {}", new_age.get(&end).unwrap().2.to_string());
                    println!("end index {}", end);
                    println!("start index {}", including.1);
                    println!(
                        "end enode {}",
                        enode_to_string(
                            &self.graph[end]
                                .node
                                .clone()
                                .map_children(|id| egraph.find(id))
                        )
                    );
                    //self.print_eclass(egraph, resulting_proof.last().unwrap(), end);
                    assert!(false);
                }
            }

            resulting_proof
        } else {
            let mut res = vec![];
            let mut counter = 0;
            for child in &left.children {
                let proof = self.take_path_including(
                    egraph,
                    rules,
                    child.clone(),
                    current_seen_memo.clone(),
                    including.clone(),
                    is_by_age,
                    should_decrease_age,
                );
                if proof.len() != 0 {
                    res = proof;
                    break;
                }
                counter += 1;
            }

            self.wrap_child_proof(&mut res, &left, counter);

            res
        }
    }

    fn wrap_child_proof(&self, proof: &mut Proof<L>, parent: &Rc<NodeExpr<L>>, child_index: usize) {
        for i in 0..proof.len() {
            let mut new_node = clone_rc(&parent);
            new_node.is_rewritten_forward = false;
            new_node.is_rewritten_backwards = false;
            for j in 0..new_node.children.len() {
                if j == child_index {
                    new_node.children[child_index] = proof[i].clone();
                } else {
                    new_node.children[j] = Rc::new(new_node.children[j].remove_rewrite_dirs());
                }
            }

            new_node.rule_ref = proof[i].rule_ref.clone();
            new_node.is_direction_forward = proof[i].is_direction_forward;

            proof[i] = Rc::new(new_node);
        }
    }

    fn build_term_age_0<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        index: usize,
    ) -> NodeExpr<L> {
        let mut children = vec![];
        let node = self.graph[index].node.clone();

        node.for_each(|child| {
            children.push(Rc::new(self.build_term_age_0(egraph, usize::from(child))));
        });

        return NodeExpr::new(node.map_children(|child| egraph.find(child)), children);
    }

    fn find_youngest_proof_path<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left_in: Rc<NodeExpr<L>>,
        right_in: Rc<NodeExpr<L>>,
        current_seen_memo: SeenMemo<L>,
    ) -> Proof<L> {
        let left = Rc::new(left_in.remove_rewrite_dirs());
        let right = Rc::new(right_in.remove_rewrite_dirs());

        let mut prev: HashMap<usize, usize> = Default::default();
        let mut prevc: HashMap<usize, &RewriteConnection<L>> = Default::default();
        let class = egraph.lookup(left.node.clone()).unwrap();
        assert_eq!(class, egraph.lookup(right.node.clone()).unwrap());
        self.find_enode_in(&left.node, class, egraph);
        self.find_enode_in(&right.node, class, egraph);
        let representative = self.find_leaf_node(*self.memo.get(&class).unwrap());
        prev.insert(representative, representative);
        let mut age = usize::MAX;
        let mut left_node = 0;
        let mut right_node = 0;
        let mut middle_node = 0;
        let left_ages = self.rec_age_calculation(egraph, &left, representative);
        let right_ages = self.rec_age_calculation(egraph, &right, representative);
        self.find_youngest_recursive(
            representative,
            egraph,
            &left,
            &right,
            &left_ages,
            &right_ages,
            &mut prev,
            &mut prevc,
            &mut age,
            &mut left_node,
            &mut right_node,
            &mut middle_node,
        );
        assert!(age < usize::MAX);
        debug!("Left age is {}", left_ages.get(&left_node).unwrap().0);
        debug!("Right age is {}", right_ages.get(&right_node).unwrap().0);
        debug!("Age is {}", age);

        if age == 0 {
            return self.apply_path(
                egraph,
                rules,
                left,
                true,
                current_seen_memo,
                (vec![], vec![]),
            );
        }

        if age == left_ages.get(&left_node).unwrap().0 {
            debug!("Taking path on left pattern");
            let mut subproof = self.take_path_including(
                egraph,
                rules,
                left,
                current_seen_memo.clone(),
                left_ages.get(&left_node).unwrap().clone(),
                true,
                true,
            );
            let middle = subproof.pop().unwrap();
            debug!("Middle before {}", middle.to_string());
            debug!("Finished left pattern");
            let mut restproof = self.find_proof_paths(
                egraph,
                rules,
                middle.clone(),
                right,
                current_seen_memo.clone(),
            );
            restproof[0] = Rc::new(restproof[0].combine_dirs(&middle));
            subproof.extend(restproof);

            return subproof;
        } else if age == right_ages.get(&right_node).unwrap().0 {
            debug!("Taking path on right pattern");
            let mut subproof = self.take_path_including(
                egraph,
                rules,
                right,
                current_seen_memo.clone(),
                right_ages.get(&right_node).unwrap().clone(),
                true,
                true,
            );
            subproof = self.reverse_proof::<N>(subproof);
            debug!("Finished right pattern");
            let mut restproof = self.find_proof_paths(
                egraph,
                rules,
                left,
                Rc::new(subproof[0].clone().remove_rewrite_dirs()),
                current_seen_memo,
            );

            let middle_prog = restproof.pop().unwrap();
            subproof[0] = Rc::new(subproof[0].combine_dirs(&middle_prog));
            restproof.extend(subproof);
            return restproof;
        } else {
            debug!("Top level path");
            let mut subproof = self.take_path_including(
                egraph,
                rules,
                left.clone(),
                current_seen_memo.clone(),
                (age, left_node, left, 0),
                true,
                false,
            );
            debug!("Finished left pattern");
            let middle = subproof.pop().unwrap();

            let mut restproof = self.find_proof_paths(
                egraph,
                rules,
                Rc::new(middle.remove_rewrite_dirs()),
                right,
                current_seen_memo.clone(),
            );
            restproof[0] = Rc::new(restproof[0].combine_dirs(&middle));
            subproof.extend(restproof);
            return subproof;
        }
    }

    fn apply_path<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left_in: Rc<NodeExpr<L>>,
        is_left_backwards: bool,
        seen_memo: SeenMemo<L>,
        (leftpath, rightpath): (Vec<&RewriteConnection<L>>, Vec<&RewriteConnection<L>>),
    ) -> Proof<L> {
        let left = Rc::new(left_in.remove_rewrite_dirs());
        let leftsize = leftpath.len();
        let rightsize = rightpath.len();
        let mut proof = vec![left.clone()];
        for i in 0..(leftsize + rightsize) {
            let connection;
            let mut is_backwards = false;
            if i < leftsize {
                connection = leftpath[i];
                is_backwards = !is_left_backwards;
            } else {
                connection = rightpath[i - leftsize];
            }
            let middle = proof.pop().unwrap();
            let ages = self.rec_age_calculation(egraph, &middle, connection.index);
            debug!(
                "Applying path age {} other side {}",
                &ages[&connection.index].0, &ages[&connection.prev].0
            );
            debug!(
                "From programs {} other side {}",
                ages[&connection.index].2.to_string(),
                &ages[&connection.prev].2.to_string()
            );
            debug!(
                "Path enodes [{}]{} and [{}]{}",
                connection.index,
                enode_to_string(&self.graph[connection.index].node),
                connection.prev,
                enode_to_string(&self.graph[connection.prev].node)
            );
            let mut subproof = self.prove_one_step(
                egraph,
                rules,
                middle.clone(),
                connection,
                seen_memo.clone(),
                is_backwards,
            );
            subproof[0] = Rc::new(subproof[0].combine_dirs(&middle));
            proof.extend(subproof);
        }

        proof
    }

    // find a sequence of rewrites between two enodes
    fn find_proof_paths<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left: Rc<NodeExpr<L>>,
        right: Rc<NodeExpr<L>>,
        seen_memo: SeenMemo<L>,
    ) -> Proof<L> {
        debug!("Prove {} and {}", left.to_string(), right.to_string());

        let seen_entry = (left.alpha_normalize(), right.alpha_normalize());

        if seen_memo.contains(&seen_entry) {
            println!("Cycle detected!!!!!!!!!!!");
            println!("Left: {}", seen_entry.0.to_string());
            println!("Right: {}", seen_entry.1.to_string());
            assert!(false);
        }
        let current_seen_memo = seen_memo.insert(seen_entry.clone());

        assert_eq!(
            egraph.lookup(left.node.clone()),
            egraph.lookup(right.node.clone())
        );

        self.find_youngest_proof_path(egraph, rules, left, right, current_seen_memo)
    }

    fn rewrite_part<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        node: Rc<NodeExpr<L>>,
        sast: &PatternAst<L>,
        rast: &PatternAst<L>,
        is_forward: bool,
    ) -> NodeExpr<L> {
        if (node.is_rewritten_forward && is_forward) || (node.is_rewritten_backwards && !is_forward)
        {
            node.rewrite::<N>(self, egraph, sast, rast, None)
        } else {
            let mut head = unwrap_or_clone(node);
            head.children = head
                .children
                .iter()
                .map(|child| {
                    Rc::new(self.rewrite_part(egraph, child.clone(), sast, rast, is_forward))
                })
                .collect();
            head
        }
    }

    fn prove_one_step<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left_in: Rc<NodeExpr<L>>,
        connection: &RewriteConnection<L>,
        seen_memo: SeenMemo<L>,
        is_backwards: bool,
    ) -> Proof<L> {
        // returns a new var_memo
        let left = Rc::new(left_in.remove_rewrite_dirs());
        let varpat = "?a".parse::<PatternAst<L>>().unwrap();

        let mut direction = connection.is_direction_forward;
        if is_backwards {
            direction = !direction;
        }

        // congruence idea- need to move children to other eclass
        if let RuleReference::Congruence(eleft_o, eright_o) = &connection.rule_ref {
            let mut eleft = eleft_o;
            let mut eright = eright_o;
            if direction {
                std::mem::swap(&mut eleft, &mut eright);
            }

            let mut proof = vec![left];

            let mut rindecies = vec![];
            eright.for_each(|child_index| rindecies.push(child_index));
            let mut counter = 0;

            eleft.for_each(|child_index| {
                let rchild_index = rindecies[counter];

                if child_index != rchild_index {
                    let middle = proof.pop().unwrap();
                    let mut subproof = self.prove_to_index(
                        egraph,
                        rules,
                        middle.children[counter].clone(),
                        seen_memo.clone(),
                        usize::from(rchild_index),
                    );
                    self.wrap_child_proof(&mut subproof, &middle, counter);
                    subproof[0] = Rc::new(subproof[0].combine_dirs(&middle));
                    proof.extend(subproof);
                }
                counter += 1;
            });

            return proof;
        }

        let mut rnode = self.graph[connection.index].node.clone();
        let mut lnode = self.graph[connection.prev].node.clone();
        if is_backwards {
            std::mem::swap(&mut rnode, &mut lnode);
        }

        let mut sast = match &connection.rule_ref {
            RuleReference::Index(i) => rules[*i]
                .searcher
                .get_ast()
                .unwrap_or_else(|| panic!("Applier must implement get_ast function")),
            RuleReference::Pattern((left, _right, _reaon)) => &left,
            RuleReference::Congruence(_l, _r) => return vec![left], // shouldn't happen
        };

        let mut rast = match &connection.rule_ref {
            RuleReference::Index(i) => rules[*i]
                .applier
                .get_ast()
                .unwrap_or_else(|| panic!("Applier must implement get_ast function")),
            RuleReference::Pattern((_left, right, _reaon)) => right,
            RuleReference::Congruence(_l, _r) => return vec![left], // shouldn't happen
        };

        if !direction {
            std::mem::swap(&mut sast, &mut rast);
        }

        debug!("Rule {} to {}", sast, rast);

        let mut search_pattern =
            NodeExpr::from_pattern_ast::<N>(self, egraph, sast, Some(&connection.subst), None);

        // if the rhs is just a variable we should adjust searcher
        if let ENodeOrVar::Var(single_var) = rast.as_ref().last().unwrap() {
            debug!("Making searcher match right enode!");
            let mut var_children = vec![];
            rnode.for_each(|child| {
                var_children.push(Rc::new(self.build_term_age_0(egraph, usize::from(child))));
            });
            let right_enode_nodeexpr = Rc::new(NodeExpr::<L>::new(
                rnode.clone().map_children(|child| egraph.find(child)),
                var_children,
            ));

            let mut rsubst: HashMap<Var, Rc<NodeExpr<L>>> = Default::default();
            rsubst.insert(*single_var, right_enode_nodeexpr);
            let new_search_pattern = NodeExpr::from_pattern_ast::<N>(
                self,
                egraph,
                sast,
                Some(&connection.subst),
                Some(&rsubst),
            );
            search_pattern = new_search_pattern;
        }

        let mut proof = self.find_proof_paths(
            egraph,
            rules,
            left.clone(),
            Rc::new(search_pattern),
            seen_memo.clone(),
        );

        let latest = proof.pop().unwrap();
        let mut next = Rc::new(latest.clone().remove_rewrite_dirs()).rewrite::<N>(
            self,
            egraph,
            sast,
            rast,
            Some(&connection.subst),
        );
        let mut newlink = unwrap_or_clone(latest.clone());
        newlink.rule_ref = connection.rule_ref.clone();
        newlink.is_direction_forward = direction;
        if direction {
            newlink.is_rewritten_forward = true;
        } else {
            next.is_rewritten_backwards = true;
        }
        proof.push(Rc::new(newlink));
        proof.push(Rc::new(next));
        proof
    }
}
