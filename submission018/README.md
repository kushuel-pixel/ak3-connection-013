# Reviewing this submission

[FORM_DESCRIPTION.txt](FORM_DESCRIPTION.txt) is the current submission text. [NOTE.md](NOTE.md) gives the mathematical argument, witnesses, distance table and evidence for each lower bound. The [reader guide](../README.md) links the cap-29 classification and gives the complete quick replay on Windows, Linux and macOS. The earlier text under evidence/012 records the draft before the Lean supplement.

## Quick replay

Run the following commands from the directory containing this guide. Python 3.12 and its standard library suffice. The first command checks the printed witness in the revised form. The second checks the archived witnesses, cycles, graph counts and stored search records.

```sh
python3 -B check_witnesses.py
python3 -B evidence/012/verify_submission.py
```

For the C++ commands to regenerate the balls and recover the cap-29 graph, see `evidence/012/REPRODUCING.md`. The full cap-30 runs require tens of GiB of disk. The two radius splits reuse the stored inner balls.

### Optional cap-30 streaming test

The small test in kit 012 exercises the search filter on cases with 0, 1 and 15 true matches. Its first case also requires a filter candidate that the exact comparison rejects. Build both test binaries with `-DFILTER_BLOCK_BITS=6` to exercise that case. The [full cap-30 search](evidence/012/REPRODUCING.md#rebuild-the-distance-bounds) uses the production default. On Linux, run this block from the directory containing this guide.

```sh
(
  set -eu
  stage="$(pwd -P)/evidence/012/stages/009"
  work=$(mktemp -d)
  cd "$work"
  g++ -std=c++17 -O3 -fopenmp "$stage/layers.cpp" -o layers
  g++ -std=c++17 -O3 -fopenmp "$stage/join.cpp" -o join
  g++ -std=c++17 -O3 -fopenmp -DFILTER_BLOCK_BITS=6 "$stage/stream_join.cpp" -o forward
  g++ -std=c++17 -O3 -fopenmp -DFILTER_BLOCK_BITS=6 -DLOW_ARITHMETIC "$stage/stream_join.cpp" -o reverse
  python3 -B "$stage/test_stream.py" ./layers ./join ./forward
  python3 -B "$stage/test_stream.py" ./layers ./join ./reverse
)
```

## Lean replay

Follow `evidence/013/REPRODUCING.md` to set up the pinned Lean 4.35.0 and mathlib project. From `evidence/013/pinned/`, run any of the following with a fresh output directory.

```sh
python3 -B ../replay.py kernel /tmp/ak3-review-kernel
python3 -B ../replay.py through26 /tmp/ak3-review-through26
python3 -B ../replay.py cap30-pilot /tmp/ak3-review-cap30-pilot
```

The first mode checks explicit words, cycles and path counts. The second additionally regenerates the native distance lower bounds through cap 26. The third checks the smaller cap-30 split. Per-declaration axioms are listed in `evidence/013/evidence/axioms.json`. The [cap-26 theorem source](evidence/013/src/Confirmed26.lean) shows which cap-30 conclusion takes a hypothesis.

Both original kits are included here with their own SHA-256 manifests. From the directory containing this guide, run `python3 -B evidence/012/verify_submission.py` to replay kit 012. The [Lean replay guide](evidence/013/REPRODUCING.md) is in kit 013.

## The exit and the renamed census input

The supplement proves the reachability equivalence for h ≥ 22, applies the ACC-P000025 certificate to separate S and E₃ at cap 28, and gives a 39-move exit into another cap-28 component. The second part transfers the distance table to ac-06945 with target τ(S). Run the following commands here to check the existing connecting and renamed paths and to enumerate the 39-move witness’s landing component. [Exit and renaming supplement](EXIT_AND_RENAMING.md)

```sh
python3 -B checks/check_transfers.py
python3 -B checks/exit025/check_landing.py
```

To reproduce the fixed-checker key comparison on Linux, run the following in the extracted directory. The check reads no closure table.

```sh
upstream_dir=$(mktemp -d)
git clone -q https://github.com/ycAlphi/andrews-curtis-cap33.git "$upstream_dir/025"
git -C "$upstream_dir/025" checkout -q fa759f65db25535e4ea244f16b86c61a815ea733
g++ -std=c++17 -O2 -pthread -I "$upstream_dir/025/code" checks/CheckStart025.cpp -o "$upstream_dir/keys"
"$upstream_dir/keys"
```

For the two additional Lean checks, build the pinned baseline and run the kernel-mode command above first. Use its output directory in place of `/tmp/ak3-review-kernel` if different. Run the following from the extracted root with Lean 4.35.0 on PATH.

```sh
root_dir=$PWD
cd evidence/013/pinned
dependency_paths=$(lake env printenv LEAN_PATH)
audit_dir=$(mktemp -d)
cp "$root_dir/checks/CountAudit.lean" "$root_dir/checks/ExitTransfer.lean" "$audit_dir/"
cd "$audit_dir"
export LEAN_PATH="$audit_dir:/tmp/ak3-review-kernel:$dependency_paths" LEAN_NUM_THREADS=1
lean -j1 -o CountAudit.olean CountAudit.lean
lean -j1 -o ExitTransfer.olean ExitTransfer.lean
leanchecker -v ExitTransfer
```

[CountAudit.log](checks/CountAudit.log) lists the transitive axioms for all five counting and pairing declarations. Each lists only propext, Classical.choice and Quot.sound. [ExitTransfer.log](checks/ExitTransfer.log) gives the axiom output for the exit theorems, and [ExitKernel.log](checks/ExitKernel.log) records the kernel replay. The [cap-28 exit replay](checks/exit025/README.md) gives the projection sources, closure commands and results for the literal endpoints. Kit 012 supplies the separate cap-30 search records.
