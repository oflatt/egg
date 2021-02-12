use crate::util::HashMap;
use crate::{
    Analysis, Applications, EGraph, ENodeOrVar, Id, Language, PatternAst, RecExpr, Rewrite, Subst,
    Var,
};
use rpds::{HashTrieMap, HashTrieSet, List};
use std::collections::VecDeque;
use std::rc::Rc;
use symbolic_expressions::Sexp;

pub type Proof<L> = Vec<Rc<NodeExpr<L>>>;

// so that creating a new path with 1 added is O(log(n))
type PathRecord<T, J> = (rpds::List<T>, HashTrieMap<T, J>);
type SeenMemo<L> = HashTrieSet<(Rc<NodeExpr<L>>, Rc<NodeExpr<L>>)>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
enum RuleReference<L> {
    Index(usize),
    Pattern((PatternAst<L>, PatternAst<L>, String)),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct RewriteConnection<L: Language> {
    pub node: L,
    subst: Subst,
    pub is_direction_forward: bool,
    rule_ref: RuleReference<L>,
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
        self.children.iter().for_each(|child| child.get_variable_refs(acc));
    }

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
        head.children = head.children.iter()
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
        var_memo: Option<&mut Vec<Rc<NodeExpr<L>>>>, // add this for variable bindings
    ) -> Self {
        let mut dummy = Default::default();
        let use_memo = var_memo != None;
        let var_memo_unwrapped = var_memo.unwrap_or(&mut dummy);
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
                                var_memo_unwrapped.push(Rc::new(NodeExpr::new(None, vec![])));
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
        (*nodeexprs.pop().unwrap()).clone()
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
        var_memo: &mut Vec<Rc<NodeExpr<L>>>,
    ) -> NodeExpr<L> {
        let mut graphsubst = Default::default();
        self.make_subst(left, Id::from(left.as_ref().len() - 1), &mut graphsubst);
        let pattern = NodeExpr::from_pattern_ast::<N>(
            egraph,
            right,
            subst,
            Some(&graphsubst),
            Some(var_memo),
        );
        pattern
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct History<L: Language> {
    // while it may have cycles, it guarantees a non-trivial path between any two enodes in an eclass
    pub graph: HashMap<L, Vec<RewriteConnection<L>>>,
}

impl<L: Language> Default for History<L> {
    fn default() -> Self {
        History::<L> {
            graph: Default::default(),
        }
    }
}

impl<L: Language> History<L> {
    fn add_connection(&mut self, from: L, to: L, rule: RuleReference<L>, subst: Subst) {
        let currentfrom = self.graph.get_mut(&from);
        let fromr = RewriteConnection {
            node: to.clone(),
            rule_ref: rule.clone(),
            subst: subst.clone(),
            is_direction_forward: true,
        };

        if let Some(v) = currentfrom {
            v.push(fromr);
        } else {
            self.graph.insert(from.clone(), vec![fromr]);
        }

        let currentto = self.graph.get_mut(&to);
        let tor = RewriteConnection {
            node: from,
            rule_ref: rule,
            subst: subst,
            is_direction_forward: false,
        };

        if let Some(v) = currentto {
            v.push(tor);
        } else {
            self.graph.insert(to, vec![tor]);
        }
    }

    pub(crate) fn add_union_proof<N: Analysis<L>>(
        &mut self,
        egraph: &mut EGraph<L, N>,
        from: PatternAst<L>,
        to: PatternAst<L>,
        subst: Subst,
        reason: String,
    ) {
        let from_node = NodeExpr::from_pattern_ast(egraph, &from, &subst, None, None);
        let to_node = NodeExpr::from_pattern_ast(egraph, &to, &subst, None, None);
        self.add_connection(
            from_node.node.unwrap(),
            to_node.node.unwrap(),
            RuleReference::Pattern((from, to, reason)),
            subst,
        );
    }

    pub(crate) fn add_applications(&mut self, applications: Applications<L>, rule: usize) {
        for (from, to, subst) in izip!(
            applications.from_nodes,
            applications.to_nodes,
            applications.substs
        ) {
            self.add_connection(from, to, RuleReference::Index(rule), subst);
        }
    }

    pub(crate) fn rebuild<N: Analysis<L>>(&mut self, egraph: &EGraph<L, N>) {
        let mut newgraph = HashMap::<L, Vec<RewriteConnection<L>>>::default();
        for (node, connections) in self.graph.iter_mut() {
            let newkey = node.clone().map_children(|child| egraph.find(child));
            connections.iter_mut().for_each(|connection| {
                connection.node.update_children(|child| egraph.find(child));
            });
            if let Some(v) = newgraph.get_mut(&newkey) {
                v.extend(connections.clone());
            } else {
                newgraph.insert(newkey, connections.clone());
            }
        }

        for (_node, connections) in newgraph.iter_mut() {
            connections.sort_unstable();
            connections.dedup();
        }

        self.graph = newgraph;
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
            let mut var_memo: Vec<Rc<NodeExpr<L>>> = Default::default();
            // push since 0 is a special value and represents no variable
            var_memo.push(Rc::new(NodeExpr::new(None, vec![])));
            let seen_memo: SeenMemo<L> = Default::default();
            return self.recursive_proof(
                egraph,
                rules,
                lg,
                rg,
                &mut var_memo,
                seen_memo
            );
        }
    }

    // find a sequence of rewrites between two enodes
    fn find_proof_path<
        N: Analysis<L>,
        F: FnMut(Vec<&RewriteConnection<L>>) -> Option<Vec<Rc<NodeExpr<L>>>>,
    >(
        &self,
        rules: &[&Rewrite<L, N>],
        left: &L,
        right: &L,
        yield_fn: &mut F,
    ) -> Option<Vec<Rc<NodeExpr<L>>>> {
        if (left == right) {
            return yield_fn(vec![]);
        }
        let dummy = RewriteConnection {
            node: left.clone(),
            rule_ref: RuleReference::Index(0),
            subst: Default::default(),
            is_direction_forward: true,
        };
        let mut todo: VecDeque<PathRecord<&L, &RewriteConnection<L>>> = VecDeque::new();
        let first_list = List::<&L>::new().push_front(left);
        let first_map = HashTrieMap::<&L, &RewriteConnection<L>>::new().insert(left, &dummy);
        todo.push_back((first_list, first_map));

        while true {
            if todo.len() == 0 {
                return None;
            }
            let (current_list, current_set) = todo.pop_front().unwrap();

            if let Some(children) = self.graph.get(current_list.first().unwrap()) {
                let mut children_iterator = children.iter();
                for child in children_iterator {
                    if current_set.contains_key(&child.node) {
                        continue;
                    }

                    let new_list = current_list.push_front(&child.node);
                    let new_map = current_set.insert(&child.node, child);
                    if &child.node == right {
                        let mut found_path = vec![];
                        let mut list_nodes = new_list.clone();
                        while list_nodes.len() > 1 {
                            let current = list_nodes.first().unwrap();
                            found_path.push(*new_map.get(current).unwrap());
                            list_nodes = list_nodes.drop_first().unwrap();
                        }
                        found_path.reverse();

                        if let Some(answer) = yield_fn(found_path) {
                            return Some(answer);
                        } else {
                            println!("###########backtracking!");
                        }
                    } else {
                        todo.push_back((new_list, new_map));
                    }
                }
            }
        }

        return None;
    }

    fn recursive_proof<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left_input: Rc<NodeExpr<L>>,
        right_input: Rc<NodeExpr<L>>,
        var_memo: &mut Vec<Rc<NodeExpr<L>>>,
        seen_memo: SeenMemo<L>,
    ) -> Option<Vec<Rc<NodeExpr<L>>>> {
        let mut left = left_input;
        let mut right = right_input;
        if (left.node == None && right.node == None) {
            panic!("Can't prove two holes equal");
        }

        // empty proof when one of them is a hole
        if left.node == None {
            // left holes could be a bound variable
            if left.var_reference > 0 {
                if var_memo[left.var_reference].node == None {
                    var_memo[left.var_reference] =  right.clone();
                    return Some(vec![right.clone()]);
                } else {
                    // found a bound variable in the expression
                    left = var_memo[left.var_reference].clone();
                }
            } else {
                return Some(vec![right.clone()]);
            }
        } else if right.node == None {
            return Some(vec![left.clone()]);
        }

        let seen_entry = (left.clone().alpha_normalize(), right.clone().alpha_normalize());
        if seen_memo.contains(&seen_entry) {
            return None;
        }

        assert_eq!(
            egraph.lookup(left.node.as_ref().unwrap().clone()),
            egraph.lookup(right.node.as_ref().unwrap().clone())
        );
        let new_seen_memo = seen_memo.insert(seen_entry.clone());

        let handle_proof_path = &mut |path: Vec<&RewriteConnection<L>>| {
            let mut proof: Vec<Rc<NodeExpr<L>>> = vec![];
            proof.push(left.clone());
            for connection in path.iter() {
                let mut sast = match &connection.rule_ref {
                    RuleReference::Index(i) => rules[*i]
                        .searcher
                        .get_ast()
                        .unwrap_or_else(|| panic!("Applier must implement get_ast function")),
                    RuleReference::Pattern((left, _right, _reaon)) => &left,
                };

                let mut rast = match &connection.rule_ref {
                    RuleReference::Index(i) => rules[*i]
                        .applier
                        .get_ast()
                        .unwrap_or_else(|| panic!("Applier must implement get_ast function")),
                    RuleReference::Pattern((_left, right, _reaon)) => right,
                };

                if !connection.is_direction_forward {
                    std::mem::swap(&mut sast, &mut rast);
                }

                //println!("rule: {} => {}", sast.to_string(), rast.to_string());

                let search_pattern = Rc::new(NodeExpr::from_pattern_ast::<N>(
                    egraph,
                    sast,
                    &connection.subst,
                    None,
                    Some(var_memo),
                ));

                // first prove it matches the search_pattern
                println!(
                    "proving {} and {}",
                    proof[proof.len() - 1].to_string(),
                    right.to_string()
                );
                println!("proving matches pattern {}", search_pattern.to_string());
                let subproof_maybe = self.recursive_proof(
                    egraph,
                    rules,
                    proof[proof.len() - 1].clone(),
                    search_pattern,
                    var_memo,
                    new_seen_memo.clone(),
                );
                if subproof_maybe == None {
                    return None;
                }
                let subproof = subproof_maybe.unwrap();
                if subproof.len() > 1 {
                    proof.pop();
                    proof.extend(subproof);
                }

                let latest = proof.pop().unwrap();
                let mut next = latest.rewrite::<N>(
                    egraph,
                    sast,
                    rast,
                    &connection.subst,
                    var_memo,
                );
                let mut newlink = (*latest).clone();
                newlink.rule_ref = connection.rule_ref.clone();
                newlink.is_direction_forward = connection.is_direction_forward;
                if connection.is_direction_forward {
                    newlink.is_rewritten_forward = true;
                } else {
                    newlink.is_rewritten_forward = false;
                }
                if !connection.is_direction_forward {
                    next.is_rewritten_backwards = true;
                } else {
                    next.is_rewritten_backwards = false;
                }
                proof.push(Rc::new(newlink));
                proof.push(Rc::new(next));
            }

            // we may have removed one layer in the expression, so prove equal again
            if proof[proof.len() - 1].node != right.node {
                let latest = proof.pop().unwrap();
                println!(
                    "proving children equal because we unwrapped {}",
                    latest.to_string()
                );
                let rest_of_proof = self.recursive_proof(
                    egraph,
                    rules,
                    latest,
                    right.clone(),
                    var_memo,
                    new_seen_memo.clone(),
                );
                if let Some(rest) = rest_of_proof {
                    proof.extend(rest);
                    Some(proof)
                } else {
                    None
                }
            } else {
                // now that we have arrived at the correct enode, there may yet be work to do on the children
                if (self.prove_children_equal(
                    egraph,
                    rules,
                    right.clone(),
                    &mut proof,
                    var_memo,
                    new_seen_memo.clone(),
                )) {
                    Some(proof)
                } else {
                    None
                }
            }
        };

        self.find_proof_path(
            rules,
            left.node.as_ref().unwrap(),
            right.node.as_ref().unwrap(),
            handle_proof_path,
        )
    }

    fn prove_children_equal<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        right: Rc<NodeExpr<L>>,
        proof: &mut Vec<Rc<NodeExpr<L>>>,
        var_memo: &mut Vec<Rc<NodeExpr<L>>>,
        seen_memo: SeenMemo<L>,
    ) -> bool {
        let left = proof[proof.len() - 1].clone();
        if left.children.len() != right.children.len() {
            panic!(
                "Found equal enodes but different number of children: {} and {}",
                left.to_string(),
                right.to_string()
            );
        }
        for i in 0..left.children.len() {
            let lchild = left.children[i].clone();
            let rchild = right.children[i].clone();
            let proof_equal_maybe = self.recursive_proof(
                egraph,
                rules,
                lchild,
                rchild,
                var_memo,
                seen_memo.clone(),
            );
            if proof_equal_maybe == None {
                return false;
            }
            let proof_equal = proof_equal_maybe.unwrap();
            let mut latest = proof.pop().unwrap();
            for j in 0..proof_equal.len() {
                let mut newlink = (*latest).clone();
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
        true
    }
}
