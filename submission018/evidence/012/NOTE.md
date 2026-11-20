# Bypassing the cap-22 bottleneck for AK(3): exact distances through cap 30

Hiromu Yasuno · Draft for review · 20 November 2026  
Follow-up to **ACC-P000024**, *From AK(3) to a fixed relator pair under length cap 22: 42 moves and 45 tokens*.

## The fixed-target question

Start at the ordered pair `A = (xyxYXY, xxxYYYY)` and end at `S = (XyyyxYYYY, xxYYYYYXyyyyy)`. Capitals denote inverse letters. Vertices are literal pairs of freely reduced words. Two vertices are equal when both words agree in order and spelling. Each of the 14 ac-r2-v1 moves costs one. Let $G_h$ be the graph induced by states of total reduced length at most $h$. The peak of a path is the largest such length, endpoints included.

At cap 22, ACC-P000024 counted 119,880 shortest ordered move-ID sequences from A to S. Every sequence passes through `U = (xYYYYXyyy, yyxxYX)` after move 35 and takes move 4 to `V = (xYYYYXyyy, yyxxYYYYYXyyy)` at move 36. Write $e$ for that single undirected edge. We delete every traversal between U and V in both directions and retain move 4 at other states. Ordinary distance and distance after deleting $e$ answer two different questions.

| Cap | Distance from A to S | Distance avoiding e |
|---|---:|---:|
| 22 | 42 | 44 |
| 23–24 | 42 | 42 |
| 25–30 | 41 | 41 |

The endpoint S itself has length 22. At this smallest possible cap, avoiding the common edge costs two extra moves. One unit of peak length removes that penalty. Three units allow a one-move improvement. A 41-move witness with peak 25 avoiding the edge appears in the [submission text](FORM_DESCRIPTION.txt).

## Why these distances are exact

Take closed search balls around A and S of radii $r,s$. On any path of length $L \le r+s$, its vertex after `min(r,L)` moves belongs to both balls. The inverse of every move is available, also after deleting the edge. Empty intersection therefore excludes every path of length up to the sum.

| Graph | Radii from A, S | Ball sizes from A, S | Excludes lengths through |
|---|---|---|---:|
| Cap 22, e deleted | 17, 26 | 5,604,126 and 5,850,123 | 43 |
| Cap 23, e deleted | 16, 25 | 18,498,477 and 19,246,060 | 41 |
| Cap 24, ordinary | 15, 26 | 19,354,365 and 32,672,025 | 41 |
| Cap 30, ordinary | 16, 24 | Stored inner radii 15 and 24, streamed one layer from A | 40 |
| Cap 30, ordinary | 15, 25 | Same stored balls, streamed one layer from S | 40 |

Each row has zero exact common states. At cap 30 the two stored balls contain 1,251,225,754 and 1,460,585,046 distinct states. The searches expand every admissible move from the outermost stored layer on the streaming side. A bit filter rejects definite misses, and the remaining candidates are compared by their complete state keys. The two split checks share the large inner balls. Their agreement checks the two outer boundaries.

The old 42-move witness at cap 22, the 44- and 42-move bypasses at caps 22 and 23, and the cap-25 bypass of length 41 give the upper bounds. Raising the cap preserves every existing path. Deleting an edge can only increase distance. These facts propagate the listed upper and lower bounds to every integer cap in the table. **Any path of at most 40 moves must attain total length at least 31.** Existence at cap 31 or at any higher peak is open here.

## Why cap 29 adds 34,624 shortest sequences

In the ordinary graph, the number of shortest 41-move sequences rises from 71,412 at cap 28 to 106,036 at cap 29. Every new sequence reaches the same state `(xYXYxy, xxxYYYY)` after move 2 and rejoins the old shortest-path graph at `(YXYYxyyyyyX, xxYYYYYXYxyyyyyX)` after move 7. Between these endpoints the following two paths share only their endpoints.

| Five move IDs, in order | Total lengths, including the endpoints |
|---|---|
| 5, 11, 3, 7, 4 | 13 → 19 → 17 → 24 → 22 → 27 |
| 3, 7, 4, 11, 2 | 13 → 20 → 18 → **29** → 27 → 27 |

There is one common two-move prefix and there are 34,624 suffixes from the rejoining state to S. Each suffix works with either segment. The four interior vertices of the higher segment are exactly the vertices added to the shortest-path graph. Going along one segment and back along the other gives a simple ten-edge cycle. A shortest sequence uses one of its two equal-length segments. This gives a bijection between the 34,624 sequences of peak exactly 27 and the 34,624 of peak exactly 29. The cap-30 count of shortest sequences remains unknown here.

The equality of endpoints also has a free-group explanation. For any starting pair $(u,v)$, let $C(w)=x^{-1}wx$ and $t=C(uv^{-1})$. Before the lower segment’s last move the pair is $(C(ut),t^{-1})$. Before the higher segment’s last move it is $(t,C(vt))$. Since $t C(vt)=C(ut)$, both final pairs are $(C(ut),C(vt))$. The specific heights and the count of suffixes come from the stated AK(3) endpoints.

### A six-move local example on the S side

Let `p = (xyXyxyXYYYYYYX, XYXYYxy)` and `q = (xyXyxyXYYYYYYX, YXyyxyx)`. Both `[3,1,3]` and `[2,1,2]` take p to q. Each arm has total lengths 21, 28, 28, 21. The four interior states are distinct. Following the first arm and reversing the second closes a six-move loop at the literal pair p. There is also a one-move route from p to q: move 1 inverts the second word and keeps the total length at 21. Thus either three-move excursion can be replaced by one move at this pair of descent states. A [replayable approach from S to p](S_SIDE_CYCLE.json) stays within cap 27. To decide whether an excursion changes the component below height 28, one must determine whether its entry and exit can reach one another at cap 27. A loop alone does not settle that question. Connectivity between S and the separate target `E₃ = (XyyyxYYYY, xxYYYYXyyyy)` at cap 28 remains open in this work.

## Scope and provenance

The new results use native search and replay. The higher-cap distance table awaits full Lean verification and external independent review. The earlier 45-token result concerns Pragyaan Gaur’s directed token system at cap 22. Higher-cap token distances, the unrestricted 14-move distance and a path to the standard pair `(x,y)` lie outside the present claims.

- Previous contribution by the author. SAIR Andrews–Curtis Challenge, Public ID **ACC-P000024**, under the title given above.
- S. Akbulut and R. Kirby, origin of the presentation family. [DOI](https://doi.org/10.1016/0040-9383%2885%2990010-2)
- SAIR competition organizers, move semantics and verifier. The replay code includes the upstream license. [Pinned verifier](https://github.com/SAIRcompetition/Andrews-Curtis/tree/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/tools/verifier)

AI assistance was used in the search, implementation, checks and drafting. [Reproduction guide](REPRODUCING.md)
