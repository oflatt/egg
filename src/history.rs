use crate::util::{HashMap};
use crate::{EClass, Id, Language, Subst, Applications
};

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
}