
Thm: For two terms `A` and `B`, the proof-producing algorithm never attempts to prove
  terms `A` and `B` equal while proving `A` and `B` equal.

Definition: A term `E` has time `t` if it was representable by the egraph at time `t`

Definition: A rewrite between two enodes `r` has time `t` if it joins
  two eclasses between time `t` and `t+1`.

Proof algorithm:
find an enode `e1`, an enode `e2`, and a path `P` between `e1` and `e2` such that:
- The oldest connection `c` in `P` has time `T`

- At time `T`, `e1` represented `A` and `e2` represented `B`

- Also at time `T`: no enodes `e3` and `e4` existed such that:
  
  `e3` represents `A`
  
  `e4` represents `B`
  
  `e3` and `e4` are in the same eclass


Proof by contradiction:

- While proving `A` equal to `B`, we apply rewrites along path `P`

- All terms and rewrites in sub-proofs will have time `t_i` <= `T`:
    - All rewrites `r_i` along path `P` have time `t_i` <= `T`
    - `A` and `B` have time `T`
    - This implies that `A` could be proven equal to `B` at time `T`
    - The proof algorithm finds the earliest proof between two terms.

- Now assume that the proof algorithm needs to prove `A` and `B` equal as a sub-proof.

- Then `A` and `B` were representable by some eclass at time `T`.

- This is a contradiction, so no sub-proof involves proving `A` and `B` equal.






