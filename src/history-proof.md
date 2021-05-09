
Thm: For two patterns `A` and `B`, the proof-producing algorithm never results in a cycle; it never attempts to prove terms `A` and `B` equal while proving `A` and `B` equal.

Def: A pattern is an expression whose leaves are either constant or an equivalence class.

Def: A pattern `E` has time `t` if it was representable by the egraph at time `t`. For an 
equivalence class, any representative counts.

Def: An application between two enodes `r` has time `t` if it joins
  two eclasses between time `t` and `t+1`.

Def: A union between two eclasses due to congruence is represented by the identity application at that time `t`.

## Proof algorithm:

Let `t_1` be the earliest time pattern `A` is representable.

Let `t_2` be the earliest time pattern`B` is representable.

There is guaranteed to be one application `c` with time `T` such that:
- At time `T`, no enodes `e_1` and `e_2` represented `A` and `B` in the same eclasses.
- At time `T+1`, enodes `e_1` and `e_2` in the same eclass represent `A` and `B` respectively

The proof algorithm performs applications along path `P`, which includes `c`:
- The application `c` happens in an eclass corresponding to a subpattern of either `A` or `B`
- So there is an enode `e_3` which represents `A` or `B`'s subpattern in this eclass.
- Since unions form a tree, there is a unique path `P` beginning at `e_3` and ending at the enode `e_4` on the other end of the application `c`.
- At each application, the proof algorithm recurs to prove the current term
equal to the left side of the application.


## Proof by contradiction that no cycles occur:
All patterns in the proof will have time `t_i` <= `T`:
- `A` and `B` both have time `t_i` <= `T`, so their subpatterns also have this property.
- All applications `r_i` along path `P` have time `t_i` <= `T`
- Applications at time `t_i` generate terms at time `t_j` <= `T`
- By induction, all intermediate terms have time `t_j` <= `T`

All patterns in sub-proofs (proofs children are equal) also have time `t_i` <= `T`
- Sub-terms have time `t` <= `T` for some `t`
- Sub-terms were known to be equal at time `T`
- The proof algorithm finds the earliest proof of two terms equal, which must have time `t` < `T`.

Now assume that the proof algorithm needs to prove `A` and `B` equal.

Then `A` and `B` were representable by the same eclass at time `T`.

This is a contradiction, so no sub-proof involves proving `A` and `B` equal.

## Proof of termination:
At each step, we consume one application with time `T`

The resulting patterns were representable by the same eclass at time `T`

This implies the proof algorithm will only take applications of time `t < T` after this step

This guarantees termination since if `T < 1` the terms must be already equal.





