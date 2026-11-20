# Bypassing the cap-22 bottleneck for AK(3) and testing shorter paths through cap 30

Hiromu Yasuno · Submission draft · 20 November 2026  
Follow-up to ACC-P000024, *From AK(3) to a fixed relator pair under length cap 22: 42 moves and 45 tokens*.

## The two thresholds

How much must the length cap increase before a shortest path can bypass an edge that every shortest path previously used? How much must it increase before the distance falls? For these endpoints the answers are one unit and three units, respectively.

Fix the ordered pairs `A = (xyxYXY, xxxYYYY)` and `S = (XyyyxYYYY, xxYYYYYXyyyyy)`. Uppercase letters denote inverses. A state is a literal pair of freely reduced words, with neither word order nor spelling identified under symmetry. Each of the 14 ac-r2-v1 moves costs one. The peak is the greatest sum of the two reduced lengths along a path, including its endpoints. Write e for the undirected edge between `U = (xYYYYXyyy, yyxxYX)` and `V = (xYYYYXyyy, yyxxYYYYYXyyy)`. Avoidance forbids all traversals between these two states in either direction. Move ID 4 remains available elsewhere.

| Cap | Ordinary distance | Distance avoiding e | Evidence for exclusion of shorter paths |
|---|---:|---:|---|
| 22 | 42 | 44 | Lean native disjoint-ball checks at cap 24 (ordinary) and cap 22 (e deleted) |
| 23–24 | 42 | 42 | Lean native ordinary cap-24 check |
| 25–26 | 41 | 41 | Lean native ordinary cap-26 check |
| 27–30 | 41 | 41 | C++ ordinary cap-30 enumeration. The Lean results give bounds of 24 through 41 in this range. |

ACC-P000024 counted 119,880 shortest 42-move sequences at cap 22. Each used move 4 from U to V on move 36. The new cap-22 theorem states that **every path of at most 43 moves crosses e**. Its conclusion specifies a crossing in either direction at some step. At cap 23 there is a 42-move bypass. At cap 25 there are two 41-move paths, one crossing e and one avoiding it.

| Witness | Moves | Peak | Steps after which the peak occurs | Traversal of e |
|---|---:|---:|---|---|
| bypass22 | 44 | 22 | 37–44 | None. It visits V after step 38. |
| bypass23 | 42 | 23 | 11–14 | None |
| bypass25 | 41 | 25 | 9 | None |
| through25 | 41 | 25 | 10 and 11 | Step 35, move 4 from U to V |

All four witnesses run from A to S. The full bypass25 move list appears in [the submission text](FORM_DESCRIPTION.txt). The Lean declarations `through25_ok` and `through25_move35` give the second cap-25 witness and its crossing.

## What the two-ball checks exclude

If a path has length L ≤ r+s, its vertex after min(r,L) moves lies within r moves of A and s moves of S. Every move has an inverse, including in the graph with e deleted. Disjoint closed balls therefore exclude lengths through r+s, inclusive. An upper bound persists when the cap is increased. A lower bound persists when the cap is decreased or e is deleted.

| Graph | Radii from A, S | Excluded lengths | Evidence |
|---|---|---:|---|
| Cap 22, e deleted | 17, 26 | ≤43 | Lean native |
| Cap 24, ordinary | 15, 26 | ≤41 | Lean native |
| Cap 26, ordinary | 16, 24 | ≤40 | Lean native |
| Cap 30, ordinary | 8, 15 | ≤23 | Lean native |
| Cap 30, ordinary | 16, 24 and 15, 25 | ≤40 | C++ with full-key comparisons |

Each Lean computation uses a native computation axiom for its disjointness result. The cap-26 lower bound gives **peak ≥27** for any A-to-S path of at most 40 moves. At cap 30, the C++ search stored 1,251,225,754 states within radius 15 of A and 1,460,585,046 within radius 24 of S. The two splits reuse those balls and stream the last layer from opposite sides. This computation gives **peak ≥31** for any such path. Whether a path of at most 40 moves exists at any peak remains open here.

In Lean, `forty_requires_31_of_cut` takes the full cap-30 disjointness claim `OrdinaryCut 30 16 24` as a hypothesis. That hypothesis is visible in the theorem type. The stored-layer lemma requires coverage through depths 15 and 24, disjoint stored balls, and exclusion of a hit after one step from the last A layer. The deposited kernel proofs cover depths 0–2 from A and 0–3 from S. The separate native 8+15 computation establishes length ≥24 at cap 30.

## The 34,624 additional lists at cap 29

On the recorded 159 states in 42 successive layers, `recorded_counts` gives exactly 71,412 sequences at cap 28 and 106,036 at cap 29. All consist of 41 ordered move IDs and end at S. The kernel also checks a list of 106,036 distinct genuine cap-29 paths. This yields a lower bound on the number of 41-move paths in the full graph. A global count of shortest paths additionally requires exclusion of shorter paths and proof that the listed layers contain every 41-move path. The C++ graph reconstruction and its reproduction steps are in kit 012. The Lean counting statements quantify over the recorded layers or assert existence of distinct paths. The count at cap 30 remains open here.

After the first two moves, 7 and 9, the path is at `(xYXYxy, xxxYYYY)`. Two five-move segments lead to the same ordered pair `(YXYYxyyyyyX, xxYYYYYXYxyyyyyX)`.

| Five move IDs | Total lengths along the segment |
|---|---|
| 5, 11, 3, 7, 4 | 13 → 19 → 17 → 24 → 22 → 27 |
| 3, 7, 4, 11, 2 | 13 → 20 → 18 → 29 → 27 → 27 |

Traversing the first segment and reversing the second gives a simple ten-move cycle. Lean proves that the two segments have equal endpoints for **every reduced starting pair**. The displayed peaks belong to this particular pair. At the rejoining state, the specified layers give 34,624 distinct 34-move continuations admissible at cap 27. For every continuation, attaching either seven-move prefix produces a pair of 41-move paths with peaks exactly 27 and 29. The theorem `paired_34624` proves this pairing directly.

The converse holds on the recorded layers. A 41-move list belongs to the cap-29 set and lies outside the cap-28 set if and only if it starts with `7 9 3 7 4 11 2` and continues with one of the specified cap-27 suffixes. Each such suffix occurs exactly once in the difference. The inclusion follows from the peak-29 prefix and the cap-27 suffix. The converse follows because the construction gives 34,624 distinct lists and the difference has size 106,036 − 71,412 = 34,624. [Classification and cap-27 companions](../review/RecordedPeak29.lean) · [Axioms](../review/recorded-axioms.log)

A separate Python check rebuilds all 14 labelled moves on the 159 recorded states without using their assigned depths. It counts 71,412, 71,412 and 106,036 length-41 lists at caps 27, 28 and 29, respectively, in both directions of counting. Both counts compute paths from A to S. [Recount](../review/recount_states.py)

## A six-move cycle on the S side

Let `p = (xyXyxyXYYYYYYX, XYXYYxy)` and `q = (xyXyxyXYYYYYYX, YXyyxyx)`. The intervals [3,1,3] and [2,1,2] each take p to q with total lengths 21 → 28 → 28 → 21. Following one and reversing the other gives a simple six-move cycle at the literal state p. Move 1 alone also takes p to q, at peak 21. An approach from S to p stays within cap 27. Thus this excursion returns to the same cap-27 component.

## Leaving the cap-28 component of S

The fixed target `E₃ = (XyyyxYYYY, xxYYYYXyyyy)` lies outside the cap-28 component of S. We applied the regenerated ACC-P000025 closure certificate to these literal endpoints, using the projection described in the supplement. A 39-move path of peak 29 reaches a different cap-28 component from S. Thus 29 is the least cap at which S can reach some other cap-28 component. Whether S reaches E₃ at cap 29 remains open. [Exit argument and 39-move witness](EXIT_AND_RENAMING.md)

## Evidence and credits

Kit 013 contains the Lean sources, pinned environment, author replay records and per-theorem axiom inventory. Path witnesses, cycles and the path-count construction use kernel proofs without a native computation axiom. The Lean distance lower bounds stated above use `decide +native`, which trusts the compiled evaluator. Kit 012 contains the C++ searches, the lightweight verifier and the instructions to regenerate the large balls. Both kits accompany this draft. The conclusions concern the fixed pair A, S and the 14-move metric. 

Hiromu Yasuno, ACC-P000024, supplies the cap-22 starting point. S. Akbulut and R. Kirby introduced the presentation family. The move table and verifier come from the SAIR organizers. AI assistance was used in the search, implementation, checks and drafting. [Akbulut–Kirby](https://doi.org/10.1016/0040-9383%2885%2990010-2) · [Pinned SAIR verifier](https://github.com/SAIRcompetition/Andrews-Curtis/tree/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/tools/verifier)
