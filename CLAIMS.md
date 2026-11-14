# Claims and evidence for submission candidate 013

The map lists ten claims and their supporting proofs, computations and Lean declarations. The manuscript explains how to apply the entry criterion during a search from S and how Lean relates a free-group endpoint to its reduced words. Section 7 lists the open cases.

## C01 Original fourteen atomic moves

Section 1; exact ordered endpoints, chronological lists, one unit per ID.

**Verification:** REVIEW007_FRESH_LOCAL_LEAN_BUILD_AND_TYPED_SCOPE; inherited contribution status retained.

Python runtime, JSON parser and official verifier implementation equivalence are outside this claim.

Evidence:

- [sources/submission001/lean/Verify/AtomicSemantics.lean](sources/submission001/lean/Verify/AtomicSemantics.lean)
- [review007/reviewers/formal/RESULT.json](review007/reviewers/formal/RESULT.json)
- [validation008/lean/RESULT.json](validation008/lean/RESULT.json)

## C02 Existing 42-move bridge with peak 22

Section 2; one fixed A-to-S certificate including all 43 prefixes.

**Verification:** REVIEW007_FRESH_LOCAL_LEAN_BUILD_AND_TYPED_SCOPE; inherited contribution status retained.

C02 certifies the displayed 42-move path and its peak of 22. The shortest-distance theorem under the length cap in [P24] and its computational assumptions are outside this audit.

Evidence:

- [sources/submission001/lean/Submission/Connections.lean](sources/submission001/lean/Submission/Connections.lean)
- [sources/submission001/evidence/BRIDGE42_CERTIFICATE.json](sources/submission001/evidence/BRIDGE42_CERTIFICATE.json)
- [review007/reviewers/formal/RESULT.json](review007/reviewers/formal/RESULT.json)
- [validation008/lean/RESULT.json](validation008/lean/RESULT.json)

Lean declarations:

- `Verify.Submission.Connections.bridge42_length`
- `Verify.Submission.Connections.bridge42_reaches`
- `Verify.Submission.Connections.bridge42_cap`
- `Verify.Submission.Connections.bridge42_attains22`
- `Verify.Submission.Connections.ak3_to_S`
- `Verify.Submission.Connections.S_to_ak3`

## C03 Unimodular entry criterion

Section 3; determinant +/-1 and FourWayHit, arbitrary ordered pair.

**Verification:** REVIEW007_FRESH_LOCAL_LEAN_BUILD_AND_TYPED_SCOPE; inherited contribution status retained.

Provides a continuation conditional on the hit. No successful prefix or cost/cap bound.

Evidence:

- [sources/submission001/lean/Extension/FourWay.lean](sources/submission001/lean/Extension/FourWay.lean)
- [sources/submission001/lean/CountedHit.lean](sources/submission001/lean/CountedHit.lean)
- [review007/reviewers/formal/RESULT.json](review007/reviewers/formal/RESULT.json)
- [validation008/lean/RESULT.json](validation008/lean/RESULT.json)

## C04 E_n reaches (x,y) in the displayed 3n+12 moves

Section 2; every natural n, including 0, canonical reduced endpoint.

**Verification:** REVIEW007_FRESH_LOCAL_LEAN_BUILD_AND_TYPED_SCOPE; inherited contribution status retained.

The specified construction is an upper bound, not a general shortestness or peak theorem.

Evidence:

- [sources/submission001/lean/Submission/EFamily.lean](sources/submission001/lean/Submission/EFamily.lean)
- [review007/reviewers/formal/RESULT.json](review007/reviewers/formal/RESULT.json)
- [validation008/lean/RESULT.json](validation008/lean/RESULT.json)

Lean declarations:

- `Verify.Submission.EFamily.run_first_Y`
- `Verify.Submission.EFamily.run_second_Y`
- `Verify.Submission.EFamily.run_second_y`
- `Verify.Submission.EFamily.prefix_run`
- `Verify.Submission.EFamily.first_mix`
- `Verify.Submission.EFamily.second_conjugations`
- `Verify.Submission.EFamily.second_mix`
- `Verify.Submission.EFamily.restore_second`
- `Verify.Submission.EFamily.suffix_run`
- `Verify.Submission.EFamily.reaches`
- `Verify.Submission.EFamily.word_length`
- `Verify.Submission.EFamily.canonical_reaches`
- `Verify.Submission.EFamily.zero_initial`

## C05 The displayed E_n construction has peak 4n+10

Section 2; exact reduced lengths of all construction blocks, every natural n including 0.

**Verification:** SELF_CONTAINED_HAND_PROOF_IN006_INDEPENDENTLY_ACCEPTED_BY_REVIEW007.

Exact peak of this construction only; all n and prefixes including n0 reviewed in007. Not Lean-formalized and not a minimum-peak claim. Old009 full archive was not retrieved.

Evidence:

- [PAPER_EN.md](PAPER_EN.md)
- [review007/reviewers/math/RESULT.json](review007/reviewers/math/RESULT.json)

## C06 Exactly four mixes imply L>=24

Section 4.1 Theorem A; fixed S and E0, all signs, arbitrary finite nonmix gaps, no word cap.

**Verification:** REVIEW007_HAND_PROOFS_INDEPENDENT_SMALL_CHECKS_AND_FRESH_COMPLETE_SCANNER_REPLAY.

Full path theorem is not Lean. Fixed S-to-E0 endpoint and exactly four mixes only; not all paths of length<=23 or all D_n endpoints. Full B15 replay in007; small checks alone do not establish its completeness.

Evidence:

- [appendix003_C1/AK3_4mix_6mix_Proof_Appendix_003_C1_en.tex](appendix003_C1/AK3_4mix_6mix_Proof_Appendix_003_C1_en.tex)
- [appendix003_C1/verification/B15_replay/RESULT.json](appendix003_C1/verification/B15_replay/RESULT.json)
- [appendix003_C1/data/common_classes.json](appendix003_C1/data/common_classes.json)
- [appendix003_C1/data/quotient_models.json](appendix003_C1/data/quotient_models.json)
- [appendix003_C1/data/dual_certificates.json](appendix003_C1/data/dual_certificates.json)
- [review007/reviewers/math/RESULT.json](review007/reviewers/math/RESULT.json)
- [review007/reviewers/compute/RESULT.json](review007/reviewers/compute/RESULT.json)

## C07 Six-mix finite inventory

Section 4.5; 4096 profiles, I244/-I16, 22 viable layouts, residual16 with156+16 profiles.

**Verification:** REVIEW007_FRESH_LOCAL_LEAN_BUILD_AND_TYPED_SCOPE; inherited contribution status retained.

Only finite definitions, counts and names. Arbitrary-path projection and semantic applicability of the removal list are not formalized.

Evidence:

- [sources/submission001/lean/Submission/SixMixFinite.lean](sources/submission001/lean/Submission/SixMixFinite.lean)
- [appendix003_C1/data/matrix_profiles.json](appendix003_C1/data/matrix_profiles.json)
- [review007/reviewers/formal/RESULT.json](review007/reviewers/formal/RESULT.json)
- [review007/reviewers/compute/RESULT.json](review007/reviewers/compute/RESULT.json)
- [validation008/lean/RESULT.json](validation008/lean/RESULT.json)

Lean declarations:

- `Verify.Submission.SixMixFinite.identity_profiles`
- `Verify.Submission.SixMixFinite.negative_identity_profiles`
- `Verify.Submission.SixMixFinite.viable_layouts`
- `Verify.Submission.SixMixFinite.residual_layouts`
- `Verify.Submission.SixMixFinite.residual_identity_profiles`
- `Verify.Submission.SixMixFinite.residual_negative_profiles`
- `Verify.Submission.SixMixFinite.residual_names`

## C08 Unbounded existential reachability equivalences

Section 3; every natural n, A-to-D_n/E_n iff S-to-standard iff existence of a reachable hit.

**Verification:** REVIEW007_FRESH_LOCAL_LEAN_BUILD_AND_TYPED_SCOPE; inherited contribution status retained.

No path witness, first-hit depth, cost preservation, cap preservation or pointwise necessity on a given path.

Evidence:

- [sources/submission001/lean/Submission/Connections.lean](sources/submission001/lean/Submission/Connections.lean)
- [review007/reviewers/formal/RESULT.json](review007/reviewers/formal/RESULT.json)
- [validation008/lean/RESULT.json](validation008/lean/RESULT.json)

Lean declarations:

- `Verify.Submission.Connections.ak3_target_iff`
- `Verify.Submission.Connections.S_standard_iff_hit`
- `Verify.Submission.Connections.member_standard`
- `Verify.Submission.Connections.E_standard`
- `Verify.Submission.Connections.S_member_iff_standard`
- `Verify.Submission.Connections.S_E_iff_standard`
- `Verify.Submission.Connections.ak3_E_iff_hit`
- `Verify.Submission.Connections.ak3_member_iff_hit`

## C09 Six-mix necessary path conditions

Section 4.1 Theorem B; fixed S/E0, original inversion and conjugation counts, C<=15 for L<=23 in -I case.

**Verification:** REVIEW007_HAND_PATH_PROOFS_AND_FINITE_LEAN_INVENTORY.

Necessary conditions, not full six-mix exclusion. The sixteen layouts and eight-plus-mix branches remain open.

Evidence:

- [appendix003_C1/AK3_4mix_6mix_Proof_Appendix_003_C1_en.tex](appendix003_C1/AK3_4mix_6mix_Proof_Appendix_003_C1_en.tex)
- [sources/submission001/lean/Submission/SixMixFinite.lean](sources/submission001/lean/Submission/SixMixFinite.lean)
- [review007/reviewers/math/RESULT.json](review007/reviewers/math/RESULT.json)
- [review007/reviewers/compute/RESULT.json](review007/reviewers/compute/RESULT.json)

## C10 Inherited D_n construction of length n+8

Section 2; every natural n, fixed D_n input and strict (x,y) endpoint.

**Verification:** REVIEW007_FRESH_LOCAL_LEAN_BUILD_AND_TYPED_SCOPE; inherited contribution status retained.

Upper bound, previously submitted as P19. Not a new general minimality claim.

Evidence:

- [sources/submission001/lean/Verify/SevenPrefix.lean](sources/submission001/lean/Verify/SevenPrefix.lean)
- [review007/reviewers/formal/RESULT.json](review007/reviewers/formal/RESULT.json)
- [validation008/lean/RESULT.json](validation008/lean/RESULT.json)
