

New idea: find the union `c` which made the two expression equal in the egraph.
Go to that eclass, run case #1. Nice!

Thm: For two patterns `A` and `B`, the proof-producing algorithm never results in a cycle;
  it never attempts to prove terms `A` and `B` equal while proving `A` and `B` equal.

Def: A pattern is an expression whose leaves are either constant or an equivalence class.

Def: A pattern `E` has time `t` if it was representable by the egraph at time `t`. For an 
equivalence class, any representative counts.

Def: A rewrite between two enodes `r` has time `t` if it joins
  two eclasses between time `t` and `t+1`.

Def: A union between two eclasses due to congruence is represented by the identity rewrite at that time `t`.

Proof algorithm:

Let `t_1` be the earliest time pattern `A` is representable.

Let `t_2` be the earliest time pattern`B` is representable.

There is guaranteed to be one rewrite `c` with time `T` such that:
- At time `T`, no enodes `e_1` and `e_2` represented `A` and `B` in the same eclasses.
- At time `T+1`, enodes `e_1` and `e_2` in the same eclass represent `A` and `B` respectively

The rewrite `c` happens in either an eclass of a subpattern of `A` or an eclass of a subpattern of `B` (choose either in the case both are true). So there is an enode `e_3` which represents `A` or `B`'s subpattern in this eclass. Since unions form a tree, there is a unique path `P` beginning at `e_3` and ending at the enode `e_4` on the other end of the rewrite `c`.

- All patterns in the proof will have time `t_i` <= `T`:
    - All rewrites `r_i` along path `P` have time `t_i` <= `T`
    - Rewrites at time `t_i` generate terms at time `t_j` <= `T`
    - By induction, all intermediate terms have time `t_j` <= `T`

## Case #1: `A` and `B` are equal because their enodes are unioned in `D`.

In this case, there exists a path `P` between `e_1` and `e_2` such that
the oldest rewrite `R` in `P` has time `T >= max(t_1, t_2)`.


- Also at time `T`, `A` and `B` were not representable by the same eclass: no enodes `e_3` and `e_4` existed such that:

  `e_3` represents `A`

  `e_4` represents `B`

  `e_3` and `e_4` are in the same eclass

- At time `T+1`, `A` and `B` known by the egraph to be equal via `e_1` and `e_2`

Proof no cycles occur:
- All patterns in the proof will have time `t_i` <= `T`:
    - All rewrites `r_i` along path `P` have time `t_i` <= `T`
    - Rewrites at time `t_i` generate terms at time `t_j` <= `T`
    - By induction, all intermediate terms have time `t_j` <= `T`

- All patterns in sub-proofs (proofs children are equal) also have time `t_i` <= `T`
    - Sub-terms have time `t` <= `T` for some `t`
    - Sub-terms were known to be equal at time `T`
    - The proof algorithm finds the earliest proof of two terms equal, which must have time `t` < `T`.

- Now assume that the proof algorithm needs to prove `A` and `B` equal.

- Then `A` and `B` were representable by the same eclass at time `T`.

- This is a contradiction, so no sub-proof involves proving `A` and `B` equal.

## Case #2: `A` and `B` are equal because their children are later found to be equal.
The proof algorithm finds the time `T` such that `A` and `B` became representable by the same
eclass for the first time at time `T+1`.

In this case, the path is in a sub-pattern of either `A` or `B`.
The algorithm performs the rewrites...



For any path `P_b` such that the oldest connection `c_b` in `P` has time `T > max(t_1, t_2)`,
`A` and `B` were already representable by the same eclass at time `T`.

So there is a path `P` between `e1` and `e2` such that the oldest connection `c` in `P` has time `t < max(t_1, t_2)`.

Proof no cycles occur:
- Consider one rewrite `A` to `A'`
- Assume congruence.
- `A` cannot contain itself. For a cycle to occur here, `A` must contain `B` and `r_1` must contain `A`
- However, either `A` or `B` must have been representable in the eclass when it wasn't before due to a union.
- `e_1` represents `A` at `T+1`, which contains term `B`. `e_1` also represents a term like `A` but with `B` at the same location. So `A` must have been directly unioned with `B`, which is a contradiction.

- Now we prove `A'` children equal to `B`
- This results in a cycle if `A'` contains `B` and `B` contains `A`
- But `A'` cannot contain `B`, since that would also imply `A` and `B` representable at time `t`





