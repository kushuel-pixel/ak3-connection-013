# Two consequences for the fixed endpoints

## The exit at each length cap

Write `P ↝ₕ Q` when a finite path of the 14 ac-r2-v1 moves takes the literal ordered pair P to Q, with total freely reduced length at most h at every state, including both endpoints. Let `T = (x,y)` and `E₃ = (XyyyxYYYY, xxYYYYXyyyy)`. For every integer h ≥ 22,

**S ↝ₕ E₃ if and only if A ↝ₕ T.**

The path from A to S takes 42 moves at peak 22. The path from E₃ to T takes 21 moves at peak 22. Append these paths at the two ends of any S-to-E₃ path. For the converse, prepend S-to-A and append T-to-E₃ to any A-to-T path. Every move has a one-move inverse, so reversing a path preserves its peak. The theorem `exit_iff` and the two witnesses can be checked in Lean. [ACC-P000024](https://competition.sair.foundation/contributor-network/acc/ACC-P000024) · [ACC-P000026](https://competition.sair.foundation/contributor-network/acc/ACC-P000026) · [Lean source](checks/ExitTransfer.lean)

### Separation at cap 28

ACC-P000025 supplied a closed set C of 8,694,374 quotient keys containing the AK(3) key and excluding the standard key. We regenerated the key file and matched its published SHA-256. The literal A and the logged representative `xyxYXY|xxxxYYY` have the same key. Applying τ(x)=Y, τ(y)=X to A gives `(YXYxyx, YYYxxxx)`; rotating each word by three letters gives the logged representative. [ACC-P000025](https://competition.sair.foundation/contributor-network/acc/ACC-P000025) · [Start-key comparisons](checks/CheckStart025.log) · [Regenerated key scan](checks/exit025/audit.json)

**S and E₃ lie in different cap-28 components.** The key of S belongs to C and the key of E₃ lies outside C. Starting in C, every admissible cap-28 move projects to the same key or an enumerated neighbour. For multiplication, Lean proves that the cyclic words can be rotated and the relative conjugator shortened to a reduced word of length at most seven with no cancellation at its junctions, or to the empty word. The proof that these cases match the C++ transition loops uses the output length bound. With S as the start and E₃ among the targets, the checker tested 238,806,300 transitions with zero closure violations. The separation uses this computation and the projection argument together. [Projection proof](checks/exit025/README.md) · [Lean normal form](checks/exit025/Junctions.lean) · [Direct closure run](checks/exit025/closure_S_E3.log)

## An exit at cap 29

Let `L = (yyyyxYXyxYYYxyyyy, YYYYXXYYYYX)`. From S, the following 39 move IDs reach L. States after moves 33 through 38 have total length 29. The last move lands at total length 28.

```text
1 12 12 12 11 4 13 11 4 9 4 3 6 8 8 8 8 3 0 6 8 13 13 13 4 9 12 12 12 10 0 7 2 11 13 13 13 13 3
```

Lean checks the endpoint, 39 moves, and the exact peak of 29. A breadth-first enumeration from L under all 14 moves at cap 28 exhausts 748 literal states and excludes S. A reader can replay both the path and this small component with `python -B checks/exit025/check_landing.py` from the directory containing this supplement. Hence 29 is the smallest peak of a path from S to L. The length 39 is a witness upper bound. **Whether a cap-29 path reaches E₃ remains open.** [Lean witness](checks/exit025/Landing39.lean) · [Small component check](checks/exit025/check_landing.py)

## One renamed census input

ACC-P000023 identifies ac-06945 with AK(3) up to renaming. The words recorded with ACC-P000028 give the literal equality `ac-06945 = (YXYxyx, YYYxxxx) = τ(A)`. The image of the target is `τ(S) = (yXXXYxxxx, YYxxxxxyXXXXX)`. [ACC-P000023](https://competition.sair.foundation/contributor-network/acc/ACC-P000023) · [ACC-P000028](https://competition.sair.foundation/contributor-network/acc/ACC-P000028) · [Pinned census](https://github.com/alejandrozarco/andrews-curtis-sair-census/tree/4839fb6703b19c37823c6ca7c1136f3f4f85d24f)

The map τ permutes the letters, respects inverse pairs and is its own inverse. Thus it commutes with free reduction and preserves length. Inversion and multiplication retain their move IDs. Conjugation by a letter becomes conjugation by its image. In order from move 0 through move 13, the image IDs are `0 1 2 3 4 5 9 8 7 6 13 12 11 10`. Applying the permutation to an exact path therefore gives a path of the same length and peak. Applying it twice recovers the original path. A traversal of e in either direction corresponds exactly to a traversal of τ(e).

It follows that the ordinary and edge-avoiding distances in the table transfer cap by cap from (A, S, e) to (ac-06945, τ(S), τ(e)). This general graph isomorphism is a paper proof. The Lean distance theorems in this package concern the original A and S. At caps 27–30 the exclusion of shorter paths still depends on the original C++ computation.

We replayed both renamed 41-move witnesses in Python, checking all 42 states of each against the images of the original path. The bypass has peak 25 only after move 9 and crosses τ(e) zero times. The other path reaches peak 25 after moves 10 and 11 and crosses from τ(U) to τ(V) on move 35 with ID 4. This gives a distance table for this one census input with the displayed transformed target. [Replay](checks/check_transfers.py) · [Output and move lists](checks/transfers.log)
