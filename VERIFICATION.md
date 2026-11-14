# Verification of submission 013

On 14 November 2026 the checks below ran on the selected files in this submission directory. The Lean runner used the fixed Lean 4.35.0 installation and previously compiled external dependencies on HOME Linux. The finite checks ran on temporary copies of the appendix. Commands are in the [reproduction guide](REPRODUCING.md).

| Check | Observed result |
|---|---|
| Source identity | All 124 copied files matched their entries in the original 013 archive. All 44 payloads in the appendix manifest passed. |
| Manuscript bindings | All ten claims have their evidence files. The 34 declaration names resolve at their listed source lines. |
| Lean | Rebuilt 31 local modules. Checked 34 complete types and their axiom sets, four inherited contracts, 20 positive examples and six expected rejections. Three modules passed replay with the same kernel. The README entry example type-checked on that build. [Lean result](git-checks/lean.json) |
| Small exact checks | Sixteen residual six-mix layouts with 156 positive-identity and 16 negative-identity profiles. All 3,364 dual columns passed. [Exact-check result](git-checks/appendix.json) |
| Full B15 replay | The preserved C++ scanners completed three positive partitions and one negative run. The positive side yielded 28,501,105 distinct forward classes and zero common classes. The negative run yielded 28,501,106 distinct forward classes and five common classes, four of cyclic length at most 32. [Full replay result](git-checks/B15.json) |

The negative scanner includes the measured `wall_seconds` in its JSON output. Its `stdout_sha256` identifies the recorded run and can change on replay. Compare the enumeration counts and the shared words, including their lengths, against the [recorded negative output](appendix003_C1/verification/B15_replay/negative.stdout.json).

These are reproduction runs for packaging. The mathematical review of the arbitrary-path reductions and the shortening lemma is recorded for the fixed 006 manuscript in review 007. [Provenance and scope](PROVENANCE.md)

## Lean with a fresh toolchain and dependency project

On Ubuntu 26.04.1 LTS (x86_64), the three Lean command blocks in the reproduction guide ran in order from an empty Elan home, an empty Lake project and empty cache directories. Elan downloaded Lean 4.35.0. Lake fetched all nine public repositories at the locked commits and unpacked 891 public mathlib cache files covering the six direct Mathlib imports. The project lockfile matched the 013 copy byte for byte. This run used the compiled public dependencies and rebuilt the 31 local proof modules.

With the fixed toolchain first on the runner's PATH, all three kernel replays passed. The runner returned exit code 0 and its result matched the [saved Lean result](git-checks/lean.json) in every field. The final command extracted the example from the checkout's README and type-checked it with the new build (exit code 0). [Fresh environment, package revisions and hashes](git-checks/fresh-deps.json)

## Claude's Lean recheck at 4f0c588

Claude reported checking out `4f0c588512d05a19b8ba8b40dfa29507413b7483` in a fresh clone and verifying the full commit ID. The run started with Elan 4.2.4 in a new home with no installed toolchains, an empty dependency cache and a clean shell environment. Claude extracted the three published Lean blocks and ran them in order in one shell. All three returned exit code 0 without additional setup. [Lean commands in this public edition](REPRODUCING.md#lean)

| Block | Elapsed (approx.) | Reported result |
|---|---:|---|
| 1. Prepare dependencies | 1 min 46 s | Installed Lean 4.35.0, fetched the nine locked public dependencies and downloaded 73 MB from the public mathlib build cache. The lockfile matched byte for byte. |
| 2. Run `run_lean.py --kernel` | 2 min 18 s | Rebuilt 31 modules and checked 34 declaration types and axiom sets, four inherited contracts, 20 positive examples and six expected rejections. The same kernel replayed EFamily, Connections and SixMixFinite successfully. The generated `RESULT.json` matched every field of the [saved result](git-checks/lean.json). |
| 3. Type-check the README example | 1 s | The example extracted from the checkout's README type-checked against the new build. |

Claude measured about 4.3 GB of disk use and about four minutes for the three blocks, including downloads. Claude reported that the earlier dependency-setup issue was resolved and found zero required corrections within this Lean recheck. The PDF and full B15 replay were outside its scope.

## Checks on the public edition

On 15 November 2026 the public runner rebuilt all 31 local modules using the fixed Lean 4.35.0 toolchain and pinned, previously compiled external dependencies. It checked all 34 declarations, passed all three kernel replays and produced a result identical to the [saved Lean result](git-checks/lean.json). The README example type-checked on this build. The exact finite checker passed, and the complete B15 replay reproduced the counts and shared classes in all four runs. [B15 results](git-checks/B15.json)

The combined PDF, manuscript, form title and description, claim and declaration maps, complete proof appendix and Lean proof sources were compared byte for byte with submission 013. The 10 claims' evidence paths and all 34 declaration locations resolve within this repository.
