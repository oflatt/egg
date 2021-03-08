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

struct PathNode<'a, L: Language> {
    pub node: &'a L,
    pub connection: &'a RewriteConnection<L>,
    pub cache_id: usize,
    pub contains: HashTrieSet<&'a L>,
    pub unique_eclass: Option<Id>,
    pub smallest_iter: usize,
}

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
    eclass: Id,
    iteration: usize,
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

pub(crate) fn unwrap_or_clone<L: Language>(node: Rc<NodeExpr<L>>) -> NodeExpr<L> {
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
    fn add_connection(
        &mut self,
        from: L,
        to: L,
        rule: RuleReference<L>,
        subst: Subst,
        eclass: Id,
        iteration: usize,
    ) {
        let currentfrom = self.graph.get_mut(&from);
        let fromr = RewriteConnection {
            node: to.clone(),
            rule_ref: rule.clone(),
            subst: subst.clone(),
            is_direction_forward: true,
            // TODO- unused for now
            iteration: 0,
            eclass: Id::from(0),
        };

        if let Some(v) = currentfrom {
            v.push(fromr);
        } else {
            self.graph.insert(from.clone(), vec![fromr]);
        }
    }

    pub(crate) fn add_union_proof<N: Analysis<L>>(
        &mut self,
        egraph: &mut EGraph<L, N>,
        eclass: Id,
        from: PatternAst<L>,
        to: PatternAst<L>,
        subst: Subst,
        reason: String,
    ) {
        let from_node = NodeExpr::from_pattern_ast(egraph, &from, &subst, None, None).0;
        let to_node = NodeExpr::from_pattern_ast(egraph, &to, &subst, None, None).0;
        self.add_connection(
            from_node.node.as_ref().unwrap().clone(),
            to_node.node.unwrap(),
            RuleReference::Pattern((from, to, reason)),
            subst,
            egraph.lookup(from_node.node.unwrap()).unwrap(),
            egraph.rebuild_count,
        );
    }

    pub(crate) fn add_applications<N: Analysis<L>>(
        &mut self,
        egraph: &mut EGraph<L, N>,
        applications: Applications<L>,
        rule: usize,
    ) {
        for (from, to, subst, class) in izip!(
            applications.from_nodes,
            applications.to_nodes,
            applications.substs,
            applications.affected_classes
        ) {
            let mut from_clone = from.clone();
            self.add_connection(
                from,
                to,
                RuleReference::Index(rule),
                subst,
                class,
                egraph.rebuild_count,
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
        }
        if let ENodeOrVar::Var(_) = pattern.as_ref().last().unwrap() {
            return true;
        } else {
            return false;
        }
    }

    // updates all enodes to be canonical
    // also adds edges going in other direction
    pub(crate) fn rebuild<N: Analysis<L>>(
        &mut self,
        egraph: &EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
    ) {
        let mut newgraph = HashMap::<L, Vec<RewriteConnection<L>>>::default();
        if self.graph.len() == 0 {
            return;
        }
        // when we rewrite an arbitrary node as in a -> (+ a 0)
        // we choose only one node to be this representative
        let mut leader_node_hash: HashMap<Id, L> = Default::default();

        let mut get_leader_node = |node: &L, replacement: &L| {
            let class = egraph.lookup(node.clone()).unwrap();
            if leader_node_hash.contains_key(&class) {
                return leader_node_hash.get(&class).unwrap().clone();
            } else {
                leader_node_hash.insert(
                    class,
                    replacement.clone().map_children(|child| egraph.find(child)),
                );
                return replacement.clone();
            }
        };

        for (node, connections) in self.graph.iter() {
            let newkey = node.clone().map_children(|child| egraph.find(child));
            let mut num_connections_left = connections.len();
            connections.iter().for_each(|connection| {
                let mut new_connection = connection.clone();
                let mut key = &newkey;
                // this code moves all arbitrary node connections to a leader node
                // it doesn't work right now because it makes paths longer
                /*let mut temp;
                if History::<L>::is_arbitrary(rules, &connection.rule_ref, true) {
                    temp = get_leader_node(node, node);
                    key = &temp;
                }
                if History::<L>::is_arbitrary(rules, &connection.rule_ref, false) {
                    new_connection.node = get_leader_node(node, &connection.node);
                } else {
                    new_connection.node.update_children(|child| egraph.find(child));
                }*/
                new_connection
                    .node
                    .update_children(|child| egraph.find(child));

                let mut other_way = new_connection.clone();
                other_way.node = key.clone();
                other_way.is_direction_forward = false;

                if let Some(v) = newgraph.get_mut(&new_connection.node) {
                    v.push(other_way);
                } else {
                    newgraph.insert(new_connection.node.clone(), vec![other_way]);
                }

                if let Some(v) = newgraph.get_mut(&key) {
                    v.push(new_connection);
                } else {
                    newgraph.insert(key.clone(), vec![new_connection]);
                }
            });
        }

        // fix nodes which have been stranded by moving rewrites to the leader node
        for (node, connections) in self.graph.iter() {
            let key = node.clone().map_children(|child| egraph.find(child));
            if newgraph.get(&key) == None || newgraph.get(&key).unwrap().len() == 0 {
                let mut new_connection = connections[0].clone();
                new_connection
                    .node
                    .update_children(|child| egraph.find(child));
                let mut other_way = new_connection.clone();
                other_way.node = key.clone();
                other_way.is_direction_forward = false;
                if let Some(v) = newgraph.get_mut(&new_connection.node) {
                    v.push(other_way);
                } else {
                    newgraph.insert(new_connection.node.clone(), vec![other_way]);
                }

                if let Some(v) = newgraph.get_mut(&key) {
                    v.push(new_connection);
                } else {
                    newgraph.insert(key, vec![new_connection]);
                }
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
        println!("Produce proof!");
        if egraph.add_expr(&left) != egraph.add_expr(&right) {
            println!("Expressions are not from same eclass!");
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
                    println!("FOUND at fuel: {}", fuel);
                    return Some(r.unwrap().0);
                } else {
                    println!("Raising fuel! New fuel: {}", fuel);
                }
            }
            return None;
        }
    }

    fn perform_proof_step<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        new_seen_memo: SeenMemo<L>,
        list_nodes: &List<PathNode<L>>,
        cache: &mut HashMap<usize, (Vec<Rc<NodeExpr<L>>>, VarMemo<L>, ExprMemo<L>)>,
        result_fail_cache: &mut ResultFailCache<L>,
        fuel: usize,
    ) -> bool {
        let next = list_nodes.first().unwrap();
        let rest_of_list = list_nodes.drop_first().unwrap();
        let node = rest_of_list.first().unwrap();

        let (partial_proof, var_memo, expr_memo) = cache.get(&node.cache_id).unwrap();

        let left_expr = partial_proof[partial_proof.len() - 1].clone();
        let step = self.prove_one_step(
            egraph,
            rules,
            left_expr.clone(),
            next.connection,
            var_memo.clone(),
            new_seen_memo.clone(),
            result_fail_cache,
            fuel,
        );
        let mut new_expr_memo = expr_memo.clone();
        if let Some((new_subproof, new_var_memo)) = step {
            let mut done = false;
            for i in 1..new_subproof.len() {
                let normalized = new_subproof[i].alpha_normalize();
                if new_expr_memo.contains(&normalized) {
                    done = true;
                    break;
                } else {
                    new_expr_memo = new_expr_memo.insert(normalized);
                }
            }
            if done {
                false
            } else {
                cache.insert(next.cache_id, (new_subproof, new_var_memo, new_expr_memo));
                true
            }
        } else {
            false
        }
    }

    fn get_iteration_of_node<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        current_node: &PathNode<L>,
        child: &RewriteConnection<L>,
    ) -> (Option<Id>, usize) {
        if current_node.cache_id == 0 {
            (Some(child.eclass), child.iteration)
        } else if current_node.unique_eclass == None {
            (None, 0)
        } else {
            let mut smaller_iter = current_node.smallest_iter;
            let mut smaller_eclass = current_node.unique_eclass.unwrap();
            let mut bigger_iter = child.iteration;
            let mut bigger_eclass = child.eclass;
            if bigger_iter < smaller_iter {
                std::mem::swap(&mut smaller_iter, &mut bigger_iter);
                std::mem::swap(&mut smaller_eclass, &mut bigger_eclass);
            }
            if let Some(dist) = egraph.distance_between(smaller_eclass, bigger_eclass) {
                if dist <= bigger_iter - smaller_iter {
                    (Some(bigger_eclass), bigger_iter)
                } else {
                    (None, 0)
                }
            } else {
                (None, 0)
            }
        }
    }

    fn finish_proof<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        new_seen_memo: SeenMemo<L>,
        cache: &HashMap<usize, (Vec<Rc<NodeExpr<L>>>, VarMemo<L>, ExprMemo<L>)>,
        list_nodes: List<PathNode<L>>,
        left: &Rc<NodeExpr<L>>,
        right: &Rc<NodeExpr<L>>,
        result_fail_cache: &mut ResultFailCache<L>,
        fuel_in: usize,
        fuel: usize,
    ) -> Option<(Vec<Rc<NodeExpr<L>>>, VarMemo<L>)> {
        let (partial_proof, var_memo, _) = cache.get(&list_nodes.first().unwrap().cache_id).unwrap();
        let mut last_fragment = vec![];
        let mut final_var_memo = Default::default();
        let latest = partial_proof[partial_proof.len() - 1].clone();

        if partial_proof[partial_proof.len() - 1].node != right.node {
            let rest_of_proof = self.find_proof_paths(
                egraph,
                rules,
                latest,
                right.clone(),
                var_memo.clone(),
                new_seen_memo.clone(),
                result_fail_cache,
                fuel,
            );
            if let Some((a_last_fragment, a_final_var_memo)) = rest_of_proof {
                last_fragment = a_last_fragment;
                final_var_memo = a_final_var_memo;
            } else {
                return None;
            }
        } else {
            last_fragment.push(latest);
            let (success, a_final_var_memo) = self.prove_children_equal(
                egraph,
                rules,
                right.clone(),
                &mut last_fragment,
                var_memo.clone(),
                new_seen_memo.clone(),
                result_fail_cache,
                fuel_in,
            );
            if success {
                final_var_memo = a_final_var_memo;
            } else {
                return None;
            }
        }
        // now we assemble the proof and return it
        let mut entire_proof = vec![left.clone()];
        let mut iter = list_nodes.reverse();
        while iter.len() > 0 {
            entire_proof.pop();
            let sub_part = cache.get(&iter.first().unwrap().cache_id).unwrap();
            entire_proof.extend(sub_part.0.clone());
            iter = iter.drop_first().unwrap();
        }
        entire_proof.pop();
        entire_proof.extend(last_fragment);
        return Some((entire_proof, final_var_memo));
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
        println!(
            "Proving: {} and {}",
            left_input.to_string(),
            right_input.to_string()
        );
        println!("fuel: {}", fuel_in);
        if fuel_in <= 1 {
            println!("Out of fuel");
            return None;
        }
        // cost of this function
        let fuel = fuel_in - 1;

        let mut current_var_memo = var_memo;
        let (left, new_memo_1) = History::<L>::get_from_var_memo(&left_input, current_var_memo);
        current_var_memo = new_memo_1;
        let (right, new_memo_2) = History::<L>::get_from_var_memo(&right_input, current_var_memo);
        current_var_memo = new_memo_2;

        let seen_entry = (
            left.clone().alpha_normalize(),
            right.clone().alpha_normalize(),
        );
        if let Some(fail_fuel) = result_fail_cache.get(&seen_entry) {
            if(fail_fuel >= &fuel_in) {
                return None;
            }
        }
        if seen_memo.contains(&seen_entry) {
            println!("Cycle detected");
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

        let dummy = RewriteConnection {
            node: left.node.as_ref().unwrap().clone(),
            rule_ref: RuleReference::Index(0),
            subst: Default::default(),
            is_direction_forward: true,
            eclass: Id::from(0),
            iteration: 0,
        };

        // for a given node, what is the smallest iteration number such that
        // we have a path that gets to that node using a single eclass
        // built from that iteration?
        let mut smallest_iteration: HashMap<&L, usize> = Default::default();
        let mut todo: VecDeque<List<PathNode<L>>> = VecDeque::new();
        let mut cache: HashMap<usize, (Vec<Rc<NodeExpr<L>>>, VarMemo<L>, ExprMemo<L>)> =
            Default::default();
        let mut deduplication_memo: HashSet<(&L, Rc<NodeExpr<L>>)> = Default::default();
        let initial_expr_memo = ExprMemo::<L>::new().insert(left.alpha_normalize());
        cache.insert(
            0,
            (
                vec![left.clone()],
                current_var_memo.clone(),
                initial_expr_memo,
            ),
        );
        let mut cache_counter = 1;
        let first_list = List::<PathNode<L>>::new().push_front(PathNode {
            node: left.node.as_ref().unwrap(),
            connection: &dummy,
            cache_id: 0,
            contains: HashTrieSet::<&L>::new().insert(left.node.as_ref().unwrap()),
            unique_eclass: None,
            smallest_iter: 0,
        });
        todo.push_back(first_list.clone());

        let mut steps = 0;
        if left.node != right.node {
            while true {
                steps += 1;
                if todo.len() == 0 {
                    break;
                }
                let current_list = todo.pop_front().unwrap();
                let current_node = current_list.first().unwrap();
                let current_expr_alpha = cache.get(&current_node.cache_id).unwrap().0.last().unwrap().alpha_normalize();
                let dedup_entry = (current_node.node, current_expr_alpha);
                if !deduplication_memo.insert(dedup_entry) {
                    continue;
                }

                if let Some(children) = self.graph.get(current_list.first().unwrap().node) {
                    let mut children_iterator = children.iter();
                    for child in children_iterator {
                        if current_node.contains.contains(&child.node) {
                            continue;
                        }

                        let (unique_class, iteration) =
                            self.get_iteration_of_node(egraph, &current_node, child);

                        /* This code greedily takes paths that are made up of smaller iterations. It isn't sound
                        if unique_class != None {
                            if let Some(best_iter) = smallest_iteration.get(&child.node) {
                                if best_iter < &iteration {
                                    continue;
                                }
                            }
                            smallest_iteration.insert(&child.node, iteration);
                        } else {
                            if let Some(best_iter) = smallest_iteration.get(&child.node) {
                                continue;
                            }
                        }*/

                        let new_node = PathNode {
                            node: &child.node,
                            connection: child,
                            cache_id: cache_counter,
                            contains: current_node.contains.insert(&child.node),
                            unique_eclass: unique_class,
                            smallest_iter: iteration,
                        };
                        cache_counter += 1;
                        let new_list = current_list.push_front(new_node);

                        if self.perform_proof_step(
                            egraph,
                            rules,
                            new_seen_memo.clone(),
                            &new_list,
                            &mut cache,
                            result_fail_cache,
                            fuel,
                        ) {
                            if &child.node == right.node.as_ref().unwrap() {
                                if let Some(proof) = self.finish_proof(
                                    egraph,
                                    rules,
                                    new_seen_memo.clone(),
                                    &cache,
                                    new_list,
                                    &left,
                                    &right,
                                    result_fail_cache,
                                    fuel_in,
                                    fuel
                                ) {
                                    return Some(proof);
                                }
                            } else {
                                todo.push_back(new_list);
                            }
                        }
                    }
                }
            }
        } else {
            return self.finish_proof(
                egraph,
                rules,
                new_seen_memo.clone(),
                &cache,
                first_list,
                &left,
                &right,
                result_fail_cache,
                fuel_in,
                fuel
            );
        }
        result_fail_cache.insert(seen_entry, fuel_in);
        return None;
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
    ) -> Option<(Vec<Rc<NodeExpr<L>>>, Vector<Rc<NodeExpr<L>>>)> {
        // returns a new var_memo
        let mut current_var_memo = var_memo;

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

        println!("rule: {} => {}", sast.to_string(), rast.to_string());

        let (search_pattern, first_var_memo) = NodeExpr::from_pattern_ast::<N>(
            egraph,
            sast,
            &connection.subst,
            None,
            Some(current_var_memo),
        );
        current_var_memo = first_var_memo;
        println!(
            "Prove one step: {} matching {} rewrite to {}",
            left.to_string(),
            search_pattern.to_string(),
            rast.to_string()
        );

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
            println!("Couldn't find subproof!");
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
