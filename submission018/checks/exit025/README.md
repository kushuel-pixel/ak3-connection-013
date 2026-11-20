# The cap-28 exit for the fixed endpoint S

For the 14 ac-r2-v1 moves on literal ordered pairs, S and E₃ lie in different connected components at total freely reduced length at most 28. Any path between them must reach total length at least 29. Existence at cap 29 is open here. The lower bound for AK(3) comes from ACC-P000025. This supplement gives a projection argument, checks the finite certificate again, and applies it directly to the two fixed endpoints.

## Finite certificate

Starting from the pinned 025 sources, we regenerated the sorted 139,109,984-byte key file. Its SHA-256 is `e62f7a0a24f993b22ec06edd625ffbbc3a9e2fa30d215b911834e1741c4aa0e4`, identical to the published digest. Call its set of 8,694,374 keys C. A separate Python reader decodes the lengths from every key. It constructs the endpoint keys by enumerating eight signed generator renamings, rotations and inversions of each cyclic word, and sorting the two words.

| Literal state | Ordered words | Key in C |
|---|---|---|
| A | `xyxYXY, xxxYYYY` | Yes |
| S | `XyyyxYYYY, xxYYYYYXyyyyy` | Yes |
| E₃ | `XyyyxYYYY, xxYYYYXyyyy` | No |
| T | `x, y` | No |
| L, the 39-move landing | `yyyyxYXyxYYYxyyyy, YYYYXXYYYYX` | No |

The published checker ran first with literal A and T and its published settings (cap 28, K=7). It ran again on the same regenerated keys with S as the literal start and E₃ and L as the two targets (cap 28, K=28). The second run allows every conjugator length feasible under the cap. Both runs checked 238,806,300 generated moves and found zero violations. They use the same implementation. [First run](closure.log) · [Direct S/E₃ run](closure_S_E3.log) · [Independent key scan](audit.json) · [Upstream sources and evidence](https://github.com/ycAlphi/andrews-curtis-cap33/tree/fa759f65db25535e4ea244f16b86c61a815ea733)

## Why every admissible exact move stays in C

Project each word to its cyclically reduced core. The key takes the two cores up to independent rotation and inversion, row exchange, and a simultaneous signed renaming. Cyclic reduction can only decrease the total length. The cyclically reduced representatives of a nontrivial conjugacy class differ by rotation. To see this, conjugate a cyclic word by a reduced word and inspect the letter adjacent to the core. A cancellation at either end rotates the core and shortens the conjugator. If neither end cancels, cyclic reduction removes the remaining conjugator. Inversion and the eight one-letter conjugation moves therefore preserve the key.

For multiplication, choose r as the changed row and s as the retained row. Write the freely reduced input words as `r = u a u⁻¹` and `s = v b v⁻¹`, with cyclic cores a and b. In the conjugacy class of the product, the word to inspect is `a c bᵋ c⁻¹`, where ε is either sign and `c = red(u⁻¹v)`. The initial bridge length satisfies

    2|c| + |a| + |b| ≤ |r| + |s| ≤ 28.

Every key in C has cyclic length at least 13. Thus |c| ≤ 7 whenever the input projects into C. This use of the minimum requires only the key of the current source to lie in C. Induction starts at S and uses closure at each step.

Rotate the cyclic words while shortening c whenever a junction cancels. If its first letter is z and either a begins with z or a ends in z⁻¹, replace a by the rotation obtained from z⁻¹az and remove z from the start of c. If its last letter is z and either bᵋ begins with z⁻¹ or bᵋ ends in z, replace bᵋ by the rotation obtained from z bᵋ z⁻¹ and remove that last z. Each replacement preserves the conjugacy class of the product. These four tests are exactly the four junction exclusions in the 025 checker.

* If the bridge becomes empty, the checker freely and cyclically reduces the product of the two rotations. The output length budget holds because it is the cyclic length of the exact output pair.
* If a nonempty bridge d remains, it is a subword of reduced c. The rotated factors are cyclically reduced and all four junctions are cancellation-free. The displayed product is therefore cyclically reduced as written. Its total length **including the retained row** is |a| + 2|b| + 2|d|, bounded by the exact output cap. This is precisely the length test in the nonempty-bridge branch.

Passing to the checker’s canonical input can exchange rows, rotate or invert each row, and rename both together. The loops cover either changed row, all rotations, and both multiplier signs. If the changed cyclic row was inverted, invert the entire product and rotate it. The inverse of `a⁻¹ d bᵋ d⁻¹` rotates to `a d b⁻ᵋ d⁻¹`. The new key and the retained row's key agree with the original output. The common generator renaming carries each bridge to one of equal length. The checker omits empty output rows. Along an exact path from S the two exponent-sum rows start as (0,−1) and (1,0), of determinant 1. The 14 moves preserve its absolute value. An empty relator is therefore impossible on the paths under consideration.

Every admissible exact move from a state projecting into C thus projects to the same key or to an enumerated neighbour. The reproduced closure check and the endpoint memberships exclude an exact cap-28 path from S to E₃. The existing Lean equivalence with A reaching T gives the same conclusion via the A/T closure run. [Exit equivalence](../ExitTransfer.lean)

## How much of K is used

Write i ≤ j for the two core lengths of a key. The greatest allowance before testing junctions or letters is achieved by retaining the shorter row. It is bounded by ⌊(28−2i−j)/2⌋. Across C the minimum of 2i+j is 19, attained at (i,j)=(5,9) and (6,7). Hence **four** is the largest positive bridge length that the nonempty-bridge loop can ever try on these keys at cap 28. Seven bounds the initial relative conjugator, and four bounds the normalized nonempty bridge admitted by the output cap. These are distinct bounds. [Key scanner](audit_keys.py)

## Lean scope

`bridge_at_28` proves the initial bound using mathlib's word decomposition. `product_formula` covers right multiplication with either sign. `junction_normal_form` rotates the factors and trims the bridge to an infix with no forbidden junction. `exact_product_at_28` combines these facts for the literal input words and proves that a conjugate representative has a reduced bridge of length at most seven. The declarations were rebuilt and replayed with Lean 4.35.0. The axiom inventory uses only propext, Classical.choice and Quot.sound. The identification with the C++ key and transition loops, the output-length argument, and the finite closure check complete the result outside Lean. The Lean files establish the indicated projection lemmas. The finite closure is a C++ computation. [Word and length lemmas](Projection.lean) · [Junction normalization](Junctions.lean) · [Axiom reports](junctions.log)

The separate theorem `landing39_ok` checks the literal endpoint L, its height 28, the 39 moves and the path’s peak 29. Its only reported axiom is `propext`. The quick replay independently checks the 39 moves and exhausts the 748-state cap-28 component of L. [Lean witness](Landing39.lean) · [Axiom report](landing39.log) · [Module replay](replay.log) · [Component check](check_landing.py)

## Reproduction

On little-endian Linux, set `here` to the absolute path of this directory. Use a fresh working directory for the generated file and the binaries.

```sh
git clone https://github.com/ycAlphi/andrews-curtis-cap33.git upstream
git -C upstream checkout --detach fa759f65db25535e4ea244f16b86c61a815ea733
g++ -O3 -std=c++17 -pthread -march=native upstream/code/ms14_engine.cpp -o search
g++ -O3 -std=c++17 -pthread -march=native upstream/code/closure_check.cpp -o checker
./search --start 'xxxYYYY|xyxYXY' --cap 28 --conj 7 --threads 6 --maxstates 12000000 --target 'x|y' --dump AK3_c28.keys
python3 "$here/audit_keys.py" AK3_c28.keys
./checker --keys AK3_c28.keys --cap 28 --conj 7 --start 'xyxYXY|xxxYYYY' --target 'x|y' --expect 8694374 --threads 6
./checker --keys AK3_c28.keys --cap 28 --conj 28 --start 'XyyyxYYYY|xxYYYYYXyyyyy' --target 'XyyyxYYYY|xxYYYYXyyyy' --target 'yyyyxYXyxYYYxyyyy|YYYYXXYYYYX' --expect 8694374 --threads 6
```

For Lean, put the pinned Lean 4.35.0 binaries on PATH. Build the [pinned 019 project](../../evidence/013/REPRODUCING.md) and run its kernel-mode replay. Set `kernel` to the absolute path of that replay’s output directory containing `FixedSWitness.olean`. From the built project run the following commands.

```sh
lake build +Mathlib.Data.List.Rotate:olean +Mathlib.Algebra.Group.Conj:olean
deps=$(lake env printenv LEAN_PATH)
work=$(mktemp -d)
cp "$here/Projection.lean" "$here/Junctions.lean" "$here/Landing39.lean" "$work/"
cd "$work"
export LEAN_PATH="$work:$kernel:$deps"
lean -j1 -o Projection.olean Projection.lean
lean -j1 -o Junctions.olean Junctions.lean
lean -j1 -o Landing39.olean Landing39.lean
leanchecker -v Projection Junctions Landing39
```
