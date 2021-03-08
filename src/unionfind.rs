use crate::Id;
use std::cell::Cell;
use std::fmt::Debug;

// The Key bound on UnionFind is necessary to derive clone. We only
// instantiate UnionFind in one place (EGraph), so this type bound
// isn't intrusive

enum Reason {
    Index(usize),
    Pattern((PatternAst<L>, PatternAst<L>, String)),
}

enum InnerReason {
    Reason(Reason),
    Congruence,
}

#[derive(Debug, Clone, Default)]
pub struct UnionFind {
    parents: Vec<Cell<Id>>,
    roots: Vec<Id>,
    enodes: Vec<L>,
    reasons: Vec<Option<InnerReason>>,
}

fn unwrap_or_clone<L: Language>(node: Rc<NodeExpr<L>>) -> NodeExpr<L> {
    match Rc::try_unwrap(node) {
        Ok(n) => n,
        Err(original) => (*original).clone(),
    }
}

impl UnionFind<L: Language> {
    pub fn make_set(&mut self) -> Id {
        let id = Id::from(self.parents.len());
        self.parents.push(Cell::new(id));
        id
    }

    pub fn make_set_with(&mut self, node: &L) -> Id {
        let id = Id::from(self.parents.len());
        self.parents.push(Cell::new(id));
        self.roots.push(id);
        self.enodes.push(node.clone());
        self.reasons.push(None);
        id
    }

    #[inline(always)]
    fn parent(&self, query: Id) -> Id {
        self.parents[usize::from(query)].get()
    }

    #[inline(always)]
    fn set_parent(&self, query: Id, new_parent: Id) {
        self.parents[usize::from(query)].set(new_parent)
    }

    #[inline(always)]
    fn root_parent(&mut self, query: Id) -> Id {
        self.roots[usize::from(query)].get()
    }

    #[inline(always)]
    fn root_set_parent(&mut self, query: Id, new_parent: Id, reason: InnerReason) {
        self.roots[usize::from(query)] = new_parent;
        self.reasons[usize::from(query)] = Some(reason);
    }

    pub fn find(&self, mut current: Id) -> Id {
        loop {
            let parent = self.parent(current);
            if current == parent {
                return parent;
            }

            current = parent;
            // do path halving and proceed
            let grandparent = self.parent(parent);
            self.set_parent(current, grandparent);
            current = grandparent;
        }
    }

    fn perform_union(&mut self, mut root1: Id, mut root2: Id) -> (Id, Id) {
        if root1 > root2 {
            // NOTE egg actuallly relied on the returned id being the minimum
            std::mem::swap(&mut root1, &mut root2);
        }
        self.set_parent(root2, root1);
        (root1, root2)
    }

    /// Returns (new_leader, old_leader)
    pub fn union(&mut self, set1: Id, set2: Id) -> (Id, Id) {
        let mut root1 = self.find(set1);
        let mut root2 = self.find(set2);

        if root1 == root2 {
            (root1, root2)
        } else {
            self.perform_union(root1, root2)
        }
    }

    /// Returns (new_leader, old_leader)
    pub fn union_with(&mut self, set1: Id, set2: Id, reason: InnerReason) -> (Id, Id) {
        let root1 = self.find(set1);
        let root2 = self.find(set2);
        if root1 == root2 {
            (root1, root2)
        } else {
            let res = self.perform_union(root1, root2);
            self.root_set_parent(root1, root2, reason);
            res
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use indexmap::{indexmap, indexset, IndexMap, IndexSet};

    impl UnionFind {
        pub fn build_sets(&self) -> IndexMap<Id, IndexSet<Id>> {
            let mut map: IndexMap<Id, IndexSet<Id>> = Default::default();

            for i in 0..self.parents.len() {
                let i = Id::from(i);
                let leader = self.find(i);
                map.entry(leader).or_default().insert(i);
            }

            map
        }
    }

    fn make_union_find(n: usize) -> UnionFind {
        let mut uf = UnionFind::default();
        for _ in 0..n {
            uf.make_set();
        }
        uf
    }

    #[test]
    fn union_find() {
        let n = 10;

        fn id(u: usize) -> Id {
            u.into()
        }

        let mut uf = make_union_find(n);

        // test the initial condition of everyone in their own set
        for i in 0..n {
            let i = Id::from(i);
            assert_eq!(uf.find(i), i);
            assert_eq!(uf.find(i), i);
        }

        // make sure build_sets works
        let expected_sets = (0..n)
            .map(|i| (id(i), indexset!(id(i))))
            .collect::<IndexMap<_, _>>();
        assert_eq!(uf.build_sets(), expected_sets);

        // build up one set
        assert_eq!(uf.union(id(0), id(1)), (id(0), id(1)));
        assert_eq!(uf.union(id(1), id(2)), (id(0), id(2)));
        assert_eq!(uf.union(id(3), id(2)), (id(0), id(3)));

        // build up another set
        assert_eq!(uf.union(id(6), id(7)), (id(6), id(7)));
        assert_eq!(uf.union(id(8), id(9)), (id(8), id(9)));
        assert_eq!(uf.union(id(7), id(9)), (id(6), id(8)));

        // make sure union on same set returns to == from
        assert_eq!(uf.union(id(1), id(3)), (id(0), id(0)));
        assert_eq!(uf.union(id(7), id(8)), (id(6), id(6)));

        // check set structure
        let expected_sets = indexmap!(
            id(0) => indexset!(id(0), id(1), id(2), id(3)),
            id(4) => indexset!(id(4)),
            id(5) => indexset!(id(5)),
            id(6) => indexset!(id(6), id(7), id(8), id(9)),
        );
        assert_eq!(uf.build_sets(), expected_sets);

        // all paths should be compressed at this point
        for i in 0..n {
            assert_eq!(uf.parent(id(i)), uf.find(id(i)));
        }
    }
}
