use std::rc::Rc;
use crate::util::{HashMap};
use crate::{Language, Subst, Applications, EGraph, Analysis, RecExpr
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct RewriteConnection<L: Language> {
  node: L,
  rule_index: usize,
  subst: Subst,
  isdirectionforward: bool,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct GraphExpr<L: Language> {
  node: Option<L>, // sometimes we have a hole
  children: Vec<Rc<GraphExpr<L>>>,
}

impl<L: Language> GraphExpr<L> {
  pub(crate) fn from_recexpr<N: Analysis<L>>(egraph: &mut EGraph::<L, N>, expr: &RecExpr<L>) -> Self {
    let nodes = expr.as_ref();
    let mut graphexprs: Vec<Rc<GraphExpr<L>>> = Vec::with_capacity(nodes.len());
    let mut new_ids = Vec::with_capacity(nodes.len());
    for node in nodes {
      let mut children: Vec<Rc<GraphExpr<L>>> = vec![];
      node.for_each(|i| children.push(graphexprs[usize::from(i)].clone()));
      let graphnode = node.clone().map_children(|i| new_ids[usize::from(i)]);
      
      let expr = Rc::new(GraphExpr { node: Some(node.clone()),
                                     children: children });
      graphexprs.push(expr);
      new_ids.push(egraph.add(graphnode));
    }
    // unwrap last graphexpr, the top node
    Rc::try_unwrap(graphexprs.pop().unwrap()).unwrap()
  }
}


pub struct History<L: Language> {
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
    for (from, to, subst) in izip!(applications.from_nodes, applications.to_nodes, applications.substs)  {
      let currentfrom = self.graph.get_mut(&from);
      let fromr = RewriteConnection { node: to.clone(), rule_index: rule, subst: subst.clone(), isdirectionforward: true};
      
      if let Some(v) = currentfrom {
        v.push(fromr);
      } else {
        self.graph.insert(from.clone(), vec![fromr]);
      }

      let currentto = self.graph.get_mut(&to);
      let tor = RewriteConnection { node: from, rule_index: rule, subst: subst, isdirectionforward: false};

      if let Some(v) = currentto {
        v.push(tor);
      } else {
        self.graph.insert(to, vec![tor]);
      }
    }
  }

  pub(crate) fn rebuild<N: Analysis<L>>(&mut self, egraph: &EGraph::<L, N>) {
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
  }
}