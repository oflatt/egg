use crate::util::{HashMap};
use crate::{Language, Subst, Applications, EGraph, Analysis
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct RewriteConnection<L: Language> {
  node: L,
  rule_index: usize,
  subst: Subst,
  isdirectionforward: bool,
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