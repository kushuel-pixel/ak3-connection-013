import Mathlib.Algebra.Group.End

/-!
# Permutation fixed-point certificates

Reusable extraction of Candidate002's generic helper section. This module depends
only on permutation group basics, not on an AK3 model, finite point data, or endpoint
obstruction. It exports fixed-point transport and the six-forward-equalities
certificate. The two proof-local algebra helpers remain private.

This is a refactoring of an existing proof, not a new AK3 nonreachability result.
Verification status is recorded separately; the original source is unchanged.
-/

namespace Verify.PermutationFixedPoint

variable {α : Type*}

/-- Conjugation transports a fixed point along the conjugating permutation. -/
theorem conjugate_fixes_of_maps (c u : Equiv.Perm α) (q p : α)
    (hu : u q = q) (hc : c q = p) :
    (c * u * c⁻¹) p = p := by
  rw [← hc]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
    Equiv.symm_apply_apply, hu]

private theorem inv_mul_apply_eq_of_eq (r b : Equiv.Perm α) (q p : α)
    (hb : b q = r p) : (r⁻¹ * b) q = p := by
  apply r.injective
  simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
    Equiv.apply_symm_apply] using hb

private theorem nested_conjugate_eq {G : Type*} [Group G] (x h r : G) :
    x * (h * r * h⁻¹) * x⁻¹ = (x * h) * r * (x * h)⁻¹ := by
  simp only [mul_inv_rev, mul_assoc]

/-- A reusable six-forward-equalities certificate, valid on any point type.
The points need not be distinct; no finiteness or decidable equality is required.
No premise asserts the desired long-word fixed-point conclusions.
-/
theorem prefix_fixes_of_six_forward_equalities
    (x r b : Equiv.Perm α) (p a e t q : α)
    (hx : x a = p) (hrp : r p = e) (hra : r a = t)
    (hrq : r q = q) (hbe : b e = e) (hbq : b q = t) :
    (x * ((r⁻¹ * b) * r * (r⁻¹ * b)⁻¹) * x⁻¹) p = p ∧
    ((r⁻¹ * b) * b * (r⁻¹ * b)⁻¹) p = p := by
  have hhq : (r⁻¹ * b) q = a :=
    inv_mul_apply_eq_of_eq r b q a (hbq.trans hra.symm)
  have hhe : (r⁻¹ * b) e = p :=
    inv_mul_apply_eq_of_eq r b e p (hbe.trans hrp.symm)
  constructor
  · rw [nested_conjugate_eq]
    apply conjugate_fixes_of_maps (x * (r⁻¹ * b)) r q p hrq
    simpa only [Equiv.Perm.mul_apply, hhq] using hx
  · exact conjugate_fixes_of_maps (r⁻¹ * b) b e p hbe hhe

end Verify.PermutationFixedPoint
