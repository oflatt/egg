use crate::util::HashMap;
use crate::{
    Analysis, Applications, EGraph, ENodeOrVar, Id, Language, PatternAst, RecExpr, Rewrite, Subst,
    Var,
};
use std::collections::VecDeque;
use std::rc::Rc;
use symbolic_expressions::Sexp;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct RewriteConnection<L: Language> {
    node: L,
    rule_index: usize,
    subst: Subst,
    is_direction_forward: bool,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct NodeExpr<L: Language> {
    node: Option<L>, // sometimes we have a hole
    children: Vec<Rc<NodeExpr<L>>>,
    rule_index: usize,
    is_direction_forward: bool,
    is_being_rewritten: bool,
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
            rule_index: 0,
            is_direction_forward: true,
            is_being_rewritten: false,
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

    pub fn to_sexp(&self) -> Sexp {
        match &self.node {
            Some(node) => {
                let op = Sexp::String(node.display_op().to_string());
                let res = {
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

                if (self.is_being_rewritten) {
                    Sexp::List(vec![Sexp::String("=>".to_string()), res])
                } else {
                    res
                }
            }
            None => Sexp::String("hole".to_string()),
        }
    }

    pub fn to_string(&self) -> String {
        self.to_sexp().to_string()
    }

    pub fn connection_string<N: Analysis<L>>(&self, rules: &[&Rewrite<L, N>]) -> String {
        if (self.is_direction_forward) {
            rules[self.rule_index].name.to_string() + &" =>".to_string()
        } else {
            "<= ".to_string() + &rules[self.rule_index].name.to_string()
        }
    }

    pub(crate) fn from_recexpr<N: Analysis<L>>(
        egraph: &mut EGraph<L, N>,
        expr: &RecExpr<L>,
    ) -> Self {
        let nodes = expr.as_ref();
        let mut graphexprs: Vec<Rc<NodeExpr<L>>> = Vec::with_capacity(nodes.len());
        let mut new_ids = Vec::with_capacity(nodes.len());
        for node in nodes {
            let mut children: Vec<Rc<NodeExpr<L>>> = vec![];
            node.for_each(|i| children.push(graphexprs[usize::from(i)].clone()));
            let graphnode = node.clone().map_children(|i| new_ids[usize::from(i)]);

            let expr = Rc::new(NodeExpr::new(Some(graphnode.clone()), children));
            graphexprs.push(expr);
            new_ids.push(egraph.add(graphnode));
        }
        // unwrap last graphexpr, the top node
        Rc::try_unwrap(graphexprs.pop().unwrap()).unwrap()
    }

    pub(crate) fn from_pattern_ast<N: Analysis<L>>(
        egraph: &mut EGraph<L, N>,
        ast: &PatternAst<L>,
        subst: &Subst,
        substmap: Option<&HashMap<Var, Rc<NodeExpr<L>>>>, // optionally used to replace variables with nodeexpr
    ) -> Self {
        let nodes = ast.as_ref();
        let mut graphexprs: Vec<Rc<NodeExpr<L>>> = Vec::with_capacity(nodes.len());
        let mut new_ids = Vec::with_capacity(nodes.len());
        for nodeorvar in nodes {
            match nodeorvar {
                ENodeOrVar::Var(v) => {
                    if let Some(map) = substmap {
                        graphexprs.push(map.get(v).unwrap().clone());
                    } else {
                        graphexprs.push(Rc::new(NodeExpr::new(None, vec![])));
                    }
                    new_ids.push(subst[*v]);
                }
                ENodeOrVar::ENode(node) => {
                    let mut children: Vec<Rc<NodeExpr<L>>> = vec![];
                    node.for_each(|i| children.push(graphexprs[usize::from(i)].clone()));
                    let graphnode = node.clone().map_children(|i| new_ids[usize::from(i)]);

                    let expr = Rc::new(NodeExpr::new(Some(graphnode.clone()), children));
                    graphexprs.push(expr);
                    new_ids.push(egraph.add(graphnode));
                }
            }
        }
        // unwrap last graphexpr, the top node
        Rc::try_unwrap(graphexprs.pop().unwrap()).unwrap()
    }

    fn make_subst(
        self: &Rc<NodeExpr<L>>,
        left: &PatternAst<L>,
        pos: Id,
        current: &mut HashMap<Var, Rc<NodeExpr<L>>>,
    ) {
        match &left[pos] {
            ENodeOrVar::Var(v) => {
                current.insert(*v, self.clone());
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
    ) -> Rc<NodeExpr<L>> {
        let mut graphsubst = Default::default();
        self.make_subst(left, Id::from(left.as_ref().len() - 1), &mut graphsubst);
        Rc::new(NodeExpr::from_pattern_ast::<N>(
            egraph,
            right,
            subst,
            Some(&graphsubst),
        ))
    }
}

pub struct History<L: Language> {
    // actually a set of trees, since each newenode is unioned only once with another enode
    graph: HashMap<L, Vec<RewriteConnection<L>>>,
}

impl<L: Language> Default for History<L> {
    fn default() -> Self {
        History::<L> {
            graph: Default::default(),
        }
    }
}

impl<L: Language> History<L> {
    pub(crate) fn add_applications(&mut self, applications: Applications<L>, rule: usize) {
        for (from, to, subst) in izip!(
            applications.from_nodes,
            applications.to_nodes,
            applications.substs
        ) {
            let currentfrom = self.graph.get_mut(&from);
            let fromr = RewriteConnection {
                node: to.clone(),
                rule_index: rule,
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
                rule_index: rule,
                subst: subst,
                is_direction_forward: false,
            };

            if let Some(v) = currentto {
                v.push(tor);
            } else {
                self.graph.insert(to, vec![tor]);
            }
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
    ) -> Option<Vec<Rc<NodeExpr<L>>>> {
        if egraph.add_expr(&left) != egraph.add_expr(&right) {
            return None;
        } else {
            let lg = Rc::new(NodeExpr::from_recexpr::<N>(egraph, left));
            let rg = Rc::new(NodeExpr::from_recexpr::<N>(egraph, right));
            return Some(self.recursive_proof(egraph, rules, lg, rg));
        }
    }

    // find a sequence of rewrites between two enodes
    // this performs a breadth first search to find the one unique path in the graph
    fn find_proof_path(&self, left: &L, right: &L) -> Vec<&RewriteConnection<L>> {
        if (left == right) {
            return vec![];
        }
        let mut prevNode: HashMap<&L, &L> = Default::default();
        let mut prev: HashMap<&L, &RewriteConnection<L>> = Default::default();
        let mut todo: VecDeque<&L> = VecDeque::new();
        todo.push_back(left);

        while true {
            if todo.len() == 0 {
                panic!("could not find proof path");
            }
            let current = todo.pop_front().unwrap();

            if let Some(children) = self.graph.get(current) {
                let mut found = false;
                for child in children {
                    prev.insert(&child.node, child);
                    prevNode.insert(&child.node, current);
                    if (&child.node == right) {
                        found = true;
                        break;
                    }
                    todo.push_back(&child.node);
                }
                if (found) {
                    break;
                }
            }
        }
        let mut path = vec![];
        let mut current: &L = right;
        while (current != left) {
            path.push(*prev.get(current).unwrap());
            current = prevNode.get(current).unwrap();
        }
        path.reverse();
        path
    }

    fn recursive_proof<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        left: Rc<NodeExpr<L>>,
        right: Rc<NodeExpr<L>>,
    ) -> Vec<Rc<NodeExpr<L>>> {
        if (left.node == None && right.node == None) {
            panic!("Can't prove two holes equal");
        }

        // empty proof when one of them is a hole
        if (left.node == None) {
            return vec![right.clone()];
        } else if (right.node == None) {
            return vec![left.clone()];
        }

        let mut proof: Vec<Rc<NodeExpr<L>>> = vec![];
        proof.push(left.clone());

        let path = self.find_proof_path(left.node.as_ref().unwrap(), right.node.as_ref().unwrap());

        for connection in path.iter() {
            if !connection.is_direction_forward {
                panic!("Rewrites from goal to start are not yet supported");
            }
            let rule = rules[connection.rule_index];
            let sast = rule.searcher.get_ast();
            if sast == None {
                panic!("Searcher must implement get_ast function");
            }
            let rast = rule.applier.get_ast();
            if rast == None {
                panic!("Applier must implement get_ast function");
            }
            let search_pattern = Rc::new(NodeExpr::from_pattern_ast::<N>(
                egraph,
                sast.unwrap(),
                &connection.subst,
                None,
            ));

            let subproof = self.recursive_proof(
                egraph,
                rules,
                proof[proof.len() - 1].clone(),
                search_pattern,
            );
            if subproof.len() > 1 {
                proof.pop();
                proof.extend(subproof);
            }

            let latest = proof.pop().unwrap();
            let next = latest.rewrite::<N>(egraph, sast.unwrap(), rast.unwrap(), &connection.subst);
            let mut newlink = (*latest).clone();
            newlink.rule_index = connection.rule_index;
            newlink.is_direction_forward = connection.is_direction_forward;
            newlink.is_being_rewritten = true;
            proof.push(Rc::new(newlink));
            proof.push(next);
        }

        // now that we have arrived at the correct enode, there may yet be work to do on the children
        self.prove_children_equal(egraph, rules, right, &mut proof);

        proof
    }

    fn prove_children_equal<N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
        rules: &[&Rewrite<L, N>],
        right: Rc<NodeExpr<L>>,
        proof: &mut Vec<Rc<NodeExpr<L>>>,
    ) {
        let left = proof[proof.len() - 1].clone();
        if left.children.len() != right.children.len() {
            panic!("Found equal enodes but different number of children");
        }
        for i in 0..left.children.len() {
            let lchild = left.children[i].clone();
            let rchild = right.children[i].clone();
            let proof_equal = self.recursive_proof(egraph, rules, lchild, rchild);
            if proof_equal.len() > 1 {
                let mut latest = proof.pop().unwrap();
                for j in 0..proof_equal.len() {
                    let mut newlink = (*latest).clone();
                    newlink.children[i] = proof_equal[j].clone();
                    newlink.rule_index = proof_equal[j].rule_index;
                    newlink.is_direction_forward = proof_equal[j].is_direction_forward;
                    proof.push(Rc::new(newlink));
                    latest = proof[proof.len() - 1].clone()
                }
            }
        }
    }
}
