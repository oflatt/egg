
Thm: For two patterns `A` and `B`, the proof-producing algorithm never results in a cycle-
  it never attempts to prove terms `A` and `B` equal while proving `A` and `B` equal.

Def: A pattern is an expression whose leaves are either constant or an equivalence class.

Def: A pattern `E` has time `t` if it was representable by the egraph at time `t`

Def: A rewrite between two enodes `r` has time `t` if it joins
  two eclasses between time `t` and `t+1`.

Proof algorithm:

Let `t_1` be the earliest time `A` is representable.

Let `t_2` be the earliest time `B` is representable.

`A` and `B` are representable in eclass `D` at the time of proof production.
They are represented by enodes `e_1` and `e_2` in `D` respectively. 



## Case #1: `A` and `B` are equal because their enodes are unioned in `D`.
In this case, there exists a path `P` between `e_1` and `e_2` such that
the oldest connection `c` in `P` has time `T >= max(t_1, t_2)`.


- Also at time `T`: no enodes `e_3` and `e_4` existed such that:
  `e_3` represents `A`
  `e_4` represents `B`
  `e_3` and `e4` are in the same eclass

So at time `T+1`, `A` and `B` known by the egraph to be equal via `e_1` and `e_2`

Proof:
- All patterns in sub-proofs will have time `t_i` <= `T`:
    - All rewrites `r_i` along path `P` have time `t_i` <= `T`
    - Rewrites at time `t_i` generate terms at time `t_j` <= `T`
    - By induction, all intermediate terms have time `t_j` <= `T`
    - Subproofs also have this property since the proof algorithm finds the earliest proof between two terms

- Now assume that the proof algorithm needs to prove `A` and `B` equal.

- Then `A` and `B` were representable by the same eclass at time `T`.

- This is a contradiction, so no sub-proof involves proving `A` and `B` equal.


## Case #2: `A` and `B` are equal because their children are found to be equal.
There is a path `P` between `e1` and `e2` such that
- The oldest connection `c` in `P` has time `t < max(t_1, t_2)`

Proof by contradiction:
- While proving `A` equal to `B`, we apply rewrites along path `P`
- Consider one rewrite `A` to `A'`
- `A` cannot contain itself but `A` can contain `B` and `r_1` can contain `A`
- Since `r_1` has time `t < T`, this is impossible because it implies `A` and `B` were representable at time `t`
- Now we prove `A'` children equal to `B`
- This results in a cycle if `A'` contains `B` and `B` contains `A`
- But `A'` cannot contain `B`, since that would also imply `A` and `B` representable at time `t` 





