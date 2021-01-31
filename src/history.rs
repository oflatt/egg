use crate::{EClass, Id, Language, Subst
};

struct RewriteConnection<L: Language> {
  node: L,
  rule_index: usize,
  subst: Subst
}

#[derive(Clone)]
pub struct History<L: Language> {
    /// The `Analysis` given when creating this `EGraph`.
    graph: HashMap<L, Vec<RewriteConnection<L>>
}