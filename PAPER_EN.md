# Entry criteria and scoped path obstructions for AK(3) and explicit trivializable families

Hiromu Yasuno

14 November 2026. Partial result.

## Abstract

An existing 42-move certificate takes the ordered AK(3) pair to
S=(R_3,B_4), while every aligned pair E_n=(R_n,B_n) has an explicit
3n+12-move trivialization in the same fourteen-atomic-move model.
The mismatch of indices matters: S is neither E_3 nor E_4, so the
family construction cannot be applied directly to S. We formulate the
remaining connection problem through a formally checked entry criterion
and unbounded reachability equivalences. These equivalences supply no
successful connection and preserve neither a cost budget nor a length cap.

A unimodular ordered pair whose cyclically reduced first or second relator
contains exactly one occurrence of either generator, counting both signs,
reaches the standard pair and every member of the specified n+8 family D_n.
In a search from S, any path that reaches such a pair can therefore be
extended to (x,y) while retaining every move already found.
Lean formalizes the E_n endpoint and 3n+12 move count for every natural n,
the existing 42-move witness with peak 22, and the connection interfaces.
The exact peak 4n+10 of the displayed E_n construction is proved by hand.

For the fixed S-to-E_0 problem, arbitrary finite nonmix gaps are allowed
and no intermediate word-length cap is imposed. Exactly four mixes require
at least 24 atomic moves. Any path from S to E_0 with exactly six mixes must
have one of sixteen residual row layouts. If its normalized matrix product
is -I and its length is at most 23, it uses at most 15 single-letter
conjugations. Lean checks the finite matrix inventory; the arbitrary-path reductions and quotient
obstructions remain hand proofs supported by exact finite computation.
These are scoped obstructions, not a complete six-mix exclusion or an
unrestricted lower bound. No path from S to a known exit is supplied.

The [claim map](CLAIMS.md) identifies the evidence and formal scope.
Complete proofs of the two path statements are in the
[proof appendix](appendix003_C1/AK3_4mix_6mix_Proof_Appendix_003_C1_en.pdf),
reproduced as Part II of the combined PDF.

## 1. Fixed objects and costs

Work in F(x,y), writing X=x^-1 and Y=y^-1. A state is an ordered pair (r,s).
The exact target is (x,y). Each of the following operations costs one move:

| ID | Next state | ID | Next state |
|---|---|---|---|
| 0 | (r^-1,s) | 1 | (r,s^-1) |
| 2 | (rs,s) | 3 | (rs^-1,s) |
| 4 | (r,sr) | 5 | (r,sr^-1) |
| 6 | (xrX,s) | 7 | (Xrx,s) |
| 8 | (yrY,s) | 9 | (Yry,s) |
| 10 | (r,xsX) | 11 | (r,Xsx) |
| 12 | (r,ysY) | 13 | (r,Ysy) |

Words are freely reduced after each move. Lists are chronological. Row swaps,
generator substitutions, and conjugations by long words are not free atomic
operations. Nonmix operations are IDs 0,1,6,...,13. A mix is one of IDs 2,...,5.
F and Q denote a mix into the first and second row, respectively. Unless an
explicit cap is stated, there is no restriction on intermediate word length.

Define

    A = (xyxYXY, xxxYYYY)
    S = (XyyyxYYYY, xxYYYYYXyyyyy)
    R_n = X y^n x Y^(n+1)
    D_n = (R_n, xY^n)
    B_n = xxY^(n+1)Xy^(n+1)
    E_n = (R_n, B_n),                         n >= 0.

The D_n notation is used here for the input family of ACC-P000019. It must not
be confused with the separate fixed-first-relator family (R_3,xY^k).
In particular D_0=(Y,x), E_0=(Y,xxYXy), and (x,y) are distinct states.
S=(R_3,B_4) is not E_3 or E_4.

The index mismatch identifies why the two positive constructions do not
already compose. A continuation from S to E_0, another E_n, or a reachable
entry hit would complete a trivialization of A. Section 3 makes the
equivalence precise for unbounded reachability. It gives no bound on the
cost or peak of the missing continuation. Theorems A and B below constrain
only the particular S-to-E_0 problem and their specified mix counts.

## 2. Positive certificates and their formal scope

The inherited D_n word is

    [9,3,6,2,2,5,11] ++ [2] repeated (n+1) times.

It ends exactly at (x,y) and has length n+8. This is an upper-bound
construction, already formalized and previously submitted [P19].

The E_n word is

    [6] ++ [9]^(n+1) ++ [5] ++ [13]^(n+1) ++ [2]
        ++ [12]^(n+1) ++ [3,4,2,5,2,8].

Here repetitions are repetitions of atomic IDs, not group powers of moves.
The word ends at (x,y) and has length 3n+12 for every natural n. These two
claims and the canonical reduced-word endpoint are formalized in
sources/submission001/lean/Submission/EFamily.lean. The all-n proof is an induction/algebraic proof, not
an extrapolation from finite replay.

For the construction's peak, put m=n+1. The initial conjugations reach

    r_c = YxY^m Xy^m,              b = xxY^m Xy^m.

Both have length 2m+3, giving total length 4m+6. ID5 changes b to xy.
After j subsequent ID13 moves the second word is Y^j x y^(j+1);
after all m such moves, ID2 changes the first word to Yxy. The m ID12
moves restore the second word to xy, and the last six moves end at (x,y).
Here is the reduced-length accounting for every block, with m>=1.
Immediately after ID6 and after j of the following m ID9 moves, for
0<=j<=m-1, the first word is y^(m-1-j)xY^mXy^j and has length 2m+1.
The last ID9 produces YxY^mXy^m, of length 2m+3. The second word still
has length 2m+3, so that state attains total length 4m+6.

After ID5 and j of the m ID13 moves, the total length is
(2m+3)+(2j+2)=2m+2j+5, for 0<=j<=m. After ID2, and j of the
m ID12 moves, the total length is 3+(2(m-j)+2)=2(m-j)+5.
The final six moves have successive total lengths 3,2,3,3,4,2,
starting from total length 5. Before ID6 the total length is 4m+4
when m>=2; for m=1 the freely reduced initial total is 6.
All these values are at most 4m+6, and the state identified above attains it.
Thus this particular construction has exact peak 4n+10, including endpoints.
For n=0 its initial pair is (Y,xxYXy), initial total length 6, and peak 10.
This is a hand proof of a construction's peak. It is neither a minimum-peak
claim nor part of the EFamily Lean endpoint and length theorems.

The positive 42-move A -> S certificate [P24] is listed in
sources/submission001/evidence/BRIDGE42_CERTIFICATE.json. sources/submission001/lean/Submission/Connections.lean replays this
same word in the existing group semantics and proves length 42, total length
at most 22 for every prefix, and attainment of 22. This preparation does not
recompute shortestness. There is no newly discovered A -> S route.

## 3. A reusable entry criterion and reachability equivalences

For g in F(x,y), let H_x(g) count x and X in the cyclic reduction of its
canonical reduced word. Let H_y be the corresponding count after swapping
the generators. Define

    Hit(r,s) : H_x(r)=1 or H_y(r)=1 or H_x(s)=1 or H_y(s)=1.

Let V(r,s) be the 2 by 2 exponent-sum matrix. The inherited formal theorem is:

    det V(r,s) in {1,-1} and Hit(r,s)
        => (r,s) reaches (x,y) and every D_m, m >= 0.

The generator and row symmetries are mapped back to the original fourteen
move IDs. They are not added as free operations. The theorem preserves an
existing prefix from S and constructs a continuation. Its hypotheses do not
assume prior reachability from S for the general-state statement.

In Lean, Reach(u,v) means that a finite list of the fourteen moves takes
the ordered pair u of free-group elements to v. For any such list starting
from reduced words, the lemma [wordRun_canonical](sources/submission001/lean/Verify/AtomicSemantics.lean)
identifies the resulting words with the canonical reduced words of the group endpoint.
For every n>=0 and either choice T_n=D_n or T_n=E_n,
the formal API proves

    Reach(A,T_n) <=> Reach(S,(x,y)) <=> exists p, Hit(run(p,S)).

The first equivalences use the existing reversible 42-move certificate and
the positive D/E trivialization words. These are unbounded equivalences.
They do not preserve a proposed length budget, cap, or shortestness claim.
Hit need not hold at every state of a successful path; the quantified
statement says that some reachable state is a hit. It supplies no successful
prefix p. Consequently it does not trivialize AK(3).

## 4. Four-mix lower bound and six-mix necessary conditions

The endpoints throughout this section are exactly
S=(XyyyxYYYY,xxYYYYYXyyyyy) and E_0=(Y,xxYXy). All fourteen moves cost
one, arbitrary finite nonmix gaps are allowed, and no intermediate word-length
cap is imposed. The letters F and Q record the row receiving a mix.

### 4.1 The two path statements

**Theorem A (four mixes).** Every path from S to E_0 containing exactly four
mix moves has atomic length L>=24.

**Theorem B (six mixes).** Every path from S to E_0 containing exactly six
mix moves has one of the sixteen layouts in Section 4.5. Its normalized
signed elementary-matrix product is I or -I. In the I case both original row
inversion counts are even; in the -I case both are odd. If L<=23, the -I case
has at most fifteen single-letter conjugations.

These are Theorems A and B of the unchanged appendix. Their complete proofs
occupy its Sections 1-8. The outline below identifies the reduction and the
finite inputs so that the statements can be read with their verification
boundaries. Theorems A and B are not full Lean path theorems.

### 4.2 Projection of an original path

For a sign s in {1,-1}, put T_F(s)=((1,s),(0,1)) and
T_Q(s)=((1,0),(s,1)). Exponent-sum matrices update by left multiplication;
the last chronological mix is therefore the leftmost factor.
The two endpoint exponent matrices are V=((0,-1),(1,0)).
Conjugations act trivially on V. Row inversions give diagonal sign matrices.
The identity T_K(s) diag(u,v)=diag(u,v) T_K(suv) pushes those signs to
the left and yields D_tot P V=V. As V is invertible and det(P)=1,
D_tot=P=I or D_tot=P=-I. This is a projection of the original path,
with its original paid inversion and conjugation counts; it is not a
replacement by a shorter path. Normalized signs need not be original mix signs.

### 4.3 Proof outline for Theorem A

The 256 four-mix layout/sign profiles have 28 products I and no products -I.
Only six layouts survive this matrix condition.

| Layouts | Reason for exclusion |
|---|---|
| The other ten four-letter layouts | No signed exponent product can reach the endpoint matrix |
| FFFF and QQQQ | The untouched row's cyclic length would change from 13 to 5 or from 9 to 1 |
| FFQQ | The S10 image killing the initial second row separates the first-row endpoint cycle types (8,1,1) and (10) |
| QQFF | The quotient BS(3,4) killing the initial first row separates the second-row endpoint conjugacy classes |
| FQQF and QFFQ | The common-word gate and central certificates below contradict L<=23 |

For QQFF the HNN proof includes the cyclic-conjugation shift r=s+4.
Britton reduction forces r=9j and then gives y^(3j+1), which is nontrivial
for every integer j. This all-integer hand argument is in Appendix Section 3;
a bounded search over conjugators does not replace it.

For either of the last two layouts, Appendix Section 4 extracts the same
oriented common conjugacy class from the original path. Use cyclic
representatives a=XyyyxYYYY, b=XyyyyyxxYYYYY, c=Y and d=XyxxY,
and define NF by free reduction, cyclic reduction and the least cyclic
rotation in the order X<Y<x<y. Inverse classes are kept distinct.
For sigma=1 or -1 the common class has the form

    U=NF(a u b^sigma u^-1)=NF(c v d^sigma v^-1).

Here u and v have arbitrary length. In the negative QFFQ branch the oriented
class is inverted; its length and normal closure are unchanged.
If c1 and c2 count original single-letter conjugations before the first mix
and after the last mix, respectively, its cyclic length N satisfies
N<=22+2c1 and N<=6+2c2. As c1+c2<=L-4, one obtains N<=L+10.
The parity of the original row lengths makes N even. Thus L<=23 gives N<=32.
These cost bounds are applied before any change of witness.

Appendix Section 5 proves by a Cayley-tree argument that, for cyclically
reduced factor lengths p and q, a witness z can be replaced while preserving
the oriented product class by one of length at most

    floor(p/2)+floor(q/2)+max(0,(N-p-q)/2).

At N<=32 the factor lengths (9,13) and (1,5) therefore put both witnesses
in the reduced-word ball B15. Each side has 28,697,813 possible witnesses.
Complete positive and negative scanner records give no positive common class
and the following four negative classes within the gate:

| Class | Cyclic length | Canonical word |
|---|---|---|
| U1 | 6 | XXYYxy |
| U2 | 16 | XXYxYYYYXYxyyyyy |
| U3 | 26 | XXYYYYYxyyyyXYxYYYYXyyyyxy |
| U4 | 28 | XXYYYYxyyyyyXXYxxYYYYYXyyyxy |

The full negative scan also finds one class of length 36, which is outside
N<=32. The completeness statement depends on both the shortening proof and
the complete scans; checking four exhibited witnesses alone is insufficient.

### 4.4 Central certificates and the four-mix conclusion

For each U_i the appendix supplies an explicit group image
H_i=F_(r_i) semidirect Z that kills U_i. The four ranks are 2,6,6,7.
Both mutually inverse free-group substitutions and all endpoint images are
checked exactly. All endpoint images have stable exponent one. A conjugator
can be adjusted to stable exponent zero, while inverse orientation is
excluded by its stable exponent.

Writing the two relevant images as (W,1) and (V,1), conjugacy would require
CW=V phi(C). In a truncated noncommutative algebra over F_p, a dual
functional annihilates every column H W - V Phi(H) and takes V-W to 1.
It therefore gives the contradiction 0=1. The truncation enlarges the allowed
coefficient space and is not a cutoff on the free-group conjugator length.

| Killed class | Rank | Prime | Degree | Columns in each of two directions |
|---|---|---|---|---|
| U1 | 2 | 5 | 4 | 30 |
| U2 | 6 | 113 | 4 | 1554 |
| U3 | 6 | 17 | 2 | 42 |
| U4 | 7 | 2 | 2 | 56 |

The eight certificates check 3,364 columns and eight normalized right-hand
sides. In FQQF, killing the outer common row would force the second-row
endpoints to be conjugate up to inversion; in QFFQ it would force the
first-row endpoints to be so. The certificates exclude both possibilities
for all four classes. Together with the earlier exclusions, this proves
Theorem A. The group-image implication is a hand proof with exact finite
certificates, not a Lean theorem about arbitrary paths.

### 4.5 Six-mix layouts and the original-move budget

There are 64 layouts and 64 normalized sign choices, hence 4,096 profiles.
Exactly 244 products are I and 16 are -I, across 22 layouts. Untouched-row
cyclic lengths exclude FFFFFF and QQQQQQ. The two monotone-block quotient
arguments exclude FFFFQQ, FFQQQQ, QQFFFF and QQQQFF.
These are two untouched-row exclusions and four quotient exclusions.

| Residual layout | I profiles | -I profiles |
|---|---|---|
| FFFQQF | 12 | 0 |
| FFQFFQ | 8 | 2 |
| FFQQFF | 12 | 0 |
| FQFFQF | 8 | 2 |
| FQFQFQ | 6 | 2 |
| FQQFFF | 12 | 0 |
| FQQFQQ | 8 | 2 |
| FQQQQF | 12 | 0 |
| QFFFFQ | 12 | 0 |
| QFFQFF | 8 | 2 |
| QFFQQQ | 12 | 0 |
| QFQFQF | 6 | 2 |
| QFQQFQ | 8 | 2 |
| QQFFQQ | 12 | 0 |
| QQFQQF | 8 | 2 |
| QQQFFQ | 12 | 0 |
| Total | 156 | 16 |

The seven declarations in sources/submission001/lean/Submission/SixMixFinite.lean
check the finite inventory and the residual names by kernel evaluation.
Their removal list is data: its applicability to arbitrary paths comes from
the hand proofs above, not merely from deleting names in a program.

Let f_F and f_Q be the original row inversion counts and C the original
single-letter conjugation count. Then L=6+f_F+f_Q+C. The diagonal matrix is
diag((-1)^f_F,(-1)^f_Q), proving the parity assertion of Theorem B.
In the -I case f_F+f_Q>=2, so L<=23 implies C<=15.
The 172 profiles are necessary matrix profiles, not 172 successful paths.
All sixteen residual layouts and the eight-or-more-mix branches remain open.

### 4.6 Relation to the connection problem

Theorem A is restricted to exactly four mixes and these fixed S,E_0 endpoints.
Theorem B gives necessary conditions for exactly six mixes. Neither supplies
an S-to-exit path or excludes every path of length at most 23. Their use with
the positive A-to-S bridge does not establish AK(3) triviality or a global
shortestness theorem. In particular, S=(R_3,B_4) cannot be replaced by E_3
or E_4 in these arguments.

## 5. Relation to existing work

The E_n family is a concrete part of the Miller-Schupp framework, not a newly
resolved unknown family [L1]. With m=n+1 and w_n=Y^m x y^m X, the actual
operations [1,11] turn its second relator into Xw_n; w_n has x exponent sum
zero. The n=0 boundary is treated separately from the positive-index MS family.

For h=Y^m x one has the free-group identity

    B_n = (xy) h R_n h^-1.

The basic substitution principle [L2] therefore explains qualitative
trivializability. The quantitative contribution retained here is the exact
fourteen-atomic-move construction and its cost accounting. The prior
literature audit did not locate these exact 3n+12 and 4n+10 formulas, but this
is not an exhaustive novelty determination. The families in [L3,L4] use a
fixed word in the compared parameterized subfamily; do not identify it with
the varying w_n here.

The known D_n theorem and 42-move connection are attributed to the earlier
submissions [P19,P24]. This package adds formal coverage and an integrated
connection interface; it does not count those older results again as new
discoveries. General nonprimitive claims from an earlier literature note are
not included as new submission claims in this preparation.

## 6. Verification and reproduction

The [claim map](CLAIMS.md) and [declaration map](LEAN_DECLARATIONS.json)
give source locations, hypotheses and exact recorded axiom sets. The scope
of the executable checks is as follows.

| Mathematical claim | Lean coverage | Additional argument or data |
|---|---|---|
| Existing 42-move A-to-S witness with peak 22 | Connections: length, endpoint and all 43 prefixes | Existing certificate; no new shortestness computation |
| E_n endpoint and length 3n+12 | EFamily: every natural n, including 0 | The all-prefix peak 4n+10 is the hand proof in Section 2 |
| Entry criterion and reachability equivalences | FourWay and Connections | Unbounded existence; no successful prefix, budget or cap is supplied |
| Theorem A | No full Lean path theorem | Appendix Sections 1-7: hand proofs, complete witness-ball scans and eight dual certificates |
| Theorem B | Seven finite-inventory declarations | Arbitrary-path projection, exclusions and original move budgets remain hand proofs |

The recorded checks use Lean 4.35.0. All 34 declarations have complete
type checks and exact axiom audits; their dependencies are limited to
propext, Quot.sound and Classical.choice, with no sorryAx or custom
computation axiom in this declaration set. The 31-module local closure
was freshly built, with four inherited type contracts, twenty positive
fixtures and six intended rejection controls also checked. Three selected
modules passed replayFromImports using the same default kernel and trusted
imported environments. Fixed external compiled dependencies were reused;
the entire Mathlib/external source tree was not rebuilt.

The finite evidence includes complete positive and negative B15 witness-ball
scans and checks of all 3,364 dual columns and eight right-hand sides.
The scans replay preserved C++ implementations, not a newly written
independent full scanner. Their applicability to arbitrary witnesses
depends on the hand-proved shortening and original-path reductions.
This ordinary computation has a different trust boundary from Lean.

B15 is the ball of all 28,697,813 reduced words of length at most fifteen
in F(x,y). In the four-mix argument of Section 4.3, if the common class
has cyclic length N<=32, the shortening lemma lets us choose conjugators
u and v in B15 that give the same oriented class. For each sign, the
scans enumerate this ball separately on the two sides. The recorded replay used four sequential
runs (three positive partitions and one negative scan), each with a 4 GiB
address-space ceiling, CPU soft/hard limits of 90/91 seconds and a 150-second
wall-time limit. [Replay measurements](review007/reviewers/compute/scanner_runs/FULL_REPLAY_RESULT.json)
record elapsed time and peak resident memory separately. Resource estimates
for larger domains or S-to-exit path searches require their own benchmarks.

[REPRODUCING.md](REPRODUCING.md) gives the byte audit, exact checks and
explicit runtime/dependency bindings. [PROVENANCE.md](PROVENANCE.md)
contains the fixed source identities, dated verification and independent
AI review records, earlier comparisons, and editorial change history.
These records do not constitute external human peer review. AI assisted
drafting, implementation, formalization, documentation, verification and
scoped review; contribution decisions remain with the author.

## 7. Conclusion and open directions

The positive constructions and entry criterion isolate an unbounded
connection problem from S to a known exit. Theorems A and B describe
obstructions for one fixed endpoint E_0 and specific mix counts; they
do not resolve that connection problem or trivialize AK(3).

For six mixes, the sixteen residual layouts remain open. In particular,
the sixteen normalized -I profiles require odd inversion counts in both
original rows; under L<=23, at most fifteen single-letter conjugations
remain. Further work could construct obstructions for these cases or
find explicit paths. Matrix profiles are necessary conditions, not paths,
and any exclusion of all short paths must also cover the other mix counts.

A second direction is to investigate S-to-E_3 or S-to-E_4 connections,
other members of the exit families, or the reachable Hit set. The E_0
obstructions do not automatically transfer to these different endpoints.
Such work must track the original atomic cost and any imposed cap
separately from the unbounded reachability equivalences. Finding one
continuation would give a positive trivialization; establishing global
shortestness or a minimum peak would require additional arguments.

These theorems, implementations and verification records provide a basis
for computational searches for the remaining connections and for checking
their outcomes. A successful search can supply an explicit move sequence.
An unsuccessful search can still inform subsequent work by recording its
search conditions, the finite domain completely explored, and any portions
left incomplete by resource limits.

## References

[P19] Hiromu Yasuno (kushuel), ACC-P000019, n+8 construction and Lean formalization.

https://github.com/kushuel-pixel/acc-nplus8-lean/tree/3ce25bf13b32d31e6989ab663a913b65779624e4

[P24] Hiromu Yasuno, ACC-P000024, From AK(3) to a fixed relator pair under
length cap 22: 42 moves and 45 tokens. The positive 42-move certificate is
included by exact move list; this preparation makes no fresh shortestness claim.

[L1] C. F. Miller III and P. E. Schupp, Some presentations of the trivial
group, Contemporary Mathematics 250 (1999), 113-115.
https://doi.org/10.1090/conm/250/03848

[L2] A. D. Myasnikov, A. G. Myasnikov and V. Shpilrain, On the Andrews-Curtis
equivalence, Contemporary Mathematics 296 (2002), 183-198, Section 2.
https://web.stevens.edu/algebraic/alexeim/Publications/AC%20Conjecture/ac1.pdf

[L3] A. Shehper et al., What makes math problems hard for reinforcement
learning: a case study, arXiv:2408.15332v2.
https://arxiv.org/html/2408.15332v2

[L4] A. Lisitsa, New Andrews-Curtis trivializations for Miller-Schupp group
presentations, Examples and Counterexamples 6 (2024), 100168.
https://doi.org/10.1016/j.exco.2024.100168

The earlier audit records which versions were actually accessible and the
limits of its literature search. A fresh exhaustive literature audit has not
been performed in this preparation.

[APP] Four-mix lower bound and six-mix placement constraints, proof appendix,
13 November 2026. Included unchanged as Part II; see appendix003_C1/.
Its own bibliography supplies the HNN and Cayley-tree references used in Section 4.

