# Reviewing the fixed-target AK(3) submission

The [submission text](submission018/FORM_DESCRIPTION.txt) reports the two fixed-target distance thresholds and classifies the additional 41-move paths in the recorded layers at cap 29. The [mathematical note](submission018/NOTE.md) gives the proof outline and links to the Lean declarations. The [replay guide](submission018/README.md) covers the underlying distance and witness computations.

## What to read first

The question is when a shortest path from A to the fixed endpoint S first escapes the old compulsory edge, and when increasing the total-length cap first shortens the path. The first caps are 23 and 25, respectively. In the Lean source, `ak3` means A and `source` means the fixed endpoint S. Move IDs start at 0. The step numbers in the witness descriptions start at 1. Edge avoidance deletes both orientations of the literal edge U–V.

| Claim | First evidence to inspect | Scope |
|---|---|---|
| Cap 22 gives distances 42 / 44, caps 23–24 give 42 / 42, caps 25–26 give 41 / 41 | [Witnesses](submission018/NOTE.md) · [lower bounds through 24](submission018/evidence/013/src/Confirmed24.lean) · [caps 25–26](submission018/evidence/013/src/Confirmed26.lean) | Ordinary distance first, edge-avoiding distance second. Exact here means a witness at that length and exclusion of every shorter list. The compiled evaluator supplies the disjointness checks. |
| At cap 22 all paths of at most 43 steps cross the edge | [compulsory_through_43](submission018/evidence/013/src/EdgeNecessity.lean) | Some step and either direction. The previous shortest-path enumeration gives the stronger time/direction statement specifically at length 42. |
| At cap 30 the A-to-S distance is 41 using the C++ lower bound | [C++ commands and recorded radii](submission018/evidence/012/REPRODUCING.md) · [conditional Lean theorem](submission018/evidence/013/src/Confirmed26.lean) · [unconditional Lean lower bound](submission018/evidence/013/src/Cap30Lower.lean) | The two C++ splits reuse the inner balls. OrdinaryCut 30 16 24 is an explicit hypothesis of the full Lean implication. The smaller native computation gives length ≥24. |
| Exactly 34,624 cap-29 additions in the recorded layers, each with a unique common suffix and a cap-27 companion | [new_at_29_iff and low_companion](review/RecordedPeak29.lean) · [paired peaks and path lengths](submission018/evidence/013/src/PairedPaths.lean) · [count on the same layers](submission018/evidence/013/src/RecordedCounts.lean) | Exact classification on these layers. At least 106,036 paths of length 41 in the full cap-29 graph. Extending completeness to that graph requires an additional argument or reliance on the separate C++ reconstruction. |
| For h ≥ 22, S reaches E₃ iff A reaches (x,y) at the same cap. S and E₃ are separated at cap 28. | [Exit equivalence](submission018/checks/ExitTransfer.lean) · [Projection and closure replay](submission018/checks/exit025/README.md) | Lean checks the equivalence and the multiplication normal form. The separation also uses the correspondence with the quotient checker and the regenerated ACC-P000025 certificate. |
| At cap 29 a 39-move path from S lands in a different cap-28 component. | [Witness and component check](submission018/EXIT_AND_RENAMING.md#an-exit-at-cap-29) | The small replay enumerates all 748 states of the landing component. Reachability of E₃ at cap 29 remains open. |
| The distances transfer to ac-06945 with target τ(S) and forbidden edge τ(e) | [proof, move permutation and source data](submission018/EXIT_AND_RENAMING.md) · [path replay](submission018/checks/check_transfers.py) | The isomorphism has a paper proof and two replayed examples. The lower bounds transfer from the original A-to-S table, including its reliance on C++ at caps 27–30. The Lean distance theorems apply to the original endpoints. |

## The additional counting statement

For the fixed 41 steps on the recorded layers let R(h) be the set of distinct move lists admitted at cap h. Every list in R(29) ∖ R(28) starts with `7 9 | 3 7 4 11 2` and has a unique remaining suffix of 34 moves in the recorded cap-27 suffix layers. Conversely every such suffix occurs. Replacing those five moves by `5 11 3 7 4` yields a member of R(27) with the same suffix. The two seven-move prefixes have exact peaks 29 and 27, respectively. The suffix stays within cap 27. Both paths end at S.

The proof uses the two existing counts, monotonicity in the cap, the checked prefix states in the first seven layers, and the 34,624 distinct possible suffixes. All constructed high-prefix paths are in the recorded difference. Equal cardinalities and injectivity of attaching a fixed prefix give equality. This argument uses no enumeration of the full capped graph. [Lean file](review/RecordedPeak29.lean) · [Axiom output](review/recorded-axioms.log)

A second finite check discards the depth labels and allows every move between the 159 recorded states. Counting exactly 41 moves from A to S gives 71,412 at cap 27, 71,412 at cap 28 and 106,036 at cap 29. Forward and backward counts agree. Thus caps 27 and 28 admit the same 41-move lists on this vertex set. Its only state of total length 29 occurs on the high arm. [Layer-free Python recount](review/recount_states.py)

## Quick replay

Start in the directory containing this README and `quick.py`. Git preserves the stored line endings, including on Windows with `core.autocrlf=true`. The replay uses the Python standard library and checks file hashes, the four A-to-S witnesses, the 39-move exit and its landing component, the saved layer and search records, the two transformed paths and the recorded path counts.

On Linux or macOS run

```sh
python3 -B quick.py
```

On Windows with Git Bash and Python 3, run

```sh
PYTHONUTF8=1 python -B quick.py
```

In PowerShell, set `$env:PYTHONUTF8 = "1"` and run `python -B quick.py`. To check the root manifest separately with Git Bash, run `sha256sum --quiet -c SHA256SUMS`.

The last line is `PASS 019 recorded-layer and witness checks`. The additional enumeration reports 71,412 at cap 28, 106,036 at cap 29 and 34,624 distinct paired suffixes. This run reads the deposited data. Fresh enumeration of the large balls has separate [C++ instructions](submission018/evidence/012/REPRODUCING.md).

## Lean replay

Use Linux with the pinned Lean 4.35.0 and mathlib. Prepare the baseline as described in [013](submission018/evidence/013/REPRODUCING.md). With the pinned binaries on PATH, run the block below from the root of this reader’s copy. To reuse an already-built identical baseline, set `project` to that directory. The kernel-mode driver checks its baseline source hashes and package revisions. The audit output contains 28 declarations.

```sh
set -eu
reader=$(pwd -P)
project="$reader/submission018/evidence/013/pinned"
work=$(mktemp -d)
cd "$project"
python3 -B "$reader/submission018/evidence/013/replay.py" kernel "$work/kernel" --project "$project"
dep_paths=$(lake env printenv LEAN_PATH)
cp "$reader/submission018/checks/ExitTransfer.lean" "$reader/review/RecordedPeak29.lean" "$reader/review/ReaderScope.lean" "$work/"
cd "$work"
export LEAN_PATH="$work:$work/kernel:$dep_paths" LEAN_NUM_THREADS=1
lean -j1 -o ExitTransfer.olean ExitTransfer.lean
lean -j1 -o RecordedPeak29.olean RecordedPeak29.lean
lean -j1 -o ReaderScope.olean ReaderScope.lean
leanchecker -v ExitTransfer RecordedPeak29 ReaderScope
```

All three public declarations in RecordedPeak29 list propext, Classical.choice and Quot.sound. ReaderScope type-checks an application of the exit equivalence and of the new classification. It also tests rejection of the conditional cap-28 exclusion used without its premise and rejection of peak 28 for the concrete high arm. [Examples](review/ReaderScope.lean) · [Kernel replay](review/kernel-replay.log)

The 019 run used the original 018 archive in a fresh directory and rebuilt its kernel-mode modules with an existing pinned baseline. Its 20 stage timings total about two minutes on this host. The kernel-mode run reused the pinned dependencies. The native distance checks and the full C++ searches have separate reproduction commands. The [exit supplement](submission018/checks/exit025/README.md) gives separate commands for the 025 closure and the three exit modules. The resource records for the original native runs are [here](submission018/evidence/013/evidence/native_runs.json).
