import Verify.PermutationFixedPoint

/-! Fixed-point closure for Nielsen operations and permitted conjugations.
The conjugation case calls the existing, pinned transport component.
No finiteness, decidable equality, AK3 endpoint, or length bound is assumed.
-/
namespace Verify.PermutationFixedPointNielsen

universe u
variable {α : Type u}
abbrev Pair (α : Type u) := Equiv.Perm α × Equiv.Perm α

def BothFix (p : α) (s : Pair α) : Prop := s.1 p = p ∧ s.2 p = p

inductive Step (α : Type u) where
  | invU | invV | mulU | mulUInv | mulV | mulVInv
  | conjU (c : Equiv.Perm α) | conjV (c : Equiv.Perm α)

def act : Step α → Pair α → Pair α
  | .invU, (u,v) => (u⁻¹,v)
  | .invV, (u,v) => (u,v⁻¹)
  | .mulU, (u,v) => (u*v,v)
  | .mulUInv, (u,v) => (u*v⁻¹,v)
  | .mulV, (u,v) => (u,v*u)
  | .mulVInv, (u,v) => (u,v*u⁻¹)
  | .conjU c, (u,v) => (c*u*c⁻¹,v)
  | .conjV c, (u,v) => (u,c*v*c⁻¹)

def allowedAt (p : α) : Step α → Prop
  | .conjU c | .conjV c => c p = p
  | _ => True

def run : List (Step α) → Pair α → Pair α
  | [],s => s
  | m::ms,s => run ms (act m s)

theorem fixes_inv (u : Equiv.Perm α) (p : α) (h : u p = p) : u⁻¹ p = p := by
  calc
    u⁻¹ p = u⁻¹ (u p) := by rw [h]
    _ = p := u.symm_apply_apply p

theorem fixes_mul (u v : Equiv.Perm α) (p : α) (hu : u p = p) (hv : v p = p) :
    (u*v) p = p := by
  simp only [Equiv.Perm.mul_apply, hv, hu]

theorem fixes_conjugate (c u : Equiv.Perm α) (p : α)
    (hu : u p = p) (hc : c p = p) : (c*u*c⁻¹) p = p := by
  exact Verify.PermutationFixedPoint.conjugate_fixes_of_maps c u p p hu hc

theorem step_fixes (p : α) (m : Step α) (s : Pair α)
    (hm : allowedAt p m) (hs : BothFix p s) : BothFix p (act m s) := by
  rcases s with ⟨u,v⟩
  rcases hs with ⟨hu,hv⟩
  cases m with
  | invU => exact ⟨fixes_inv u p hu, hv⟩
  | invV => exact ⟨hu, fixes_inv v p hv⟩
  | mulU => exact ⟨fixes_mul u v p hu hv, hv⟩
  | mulUInv => exact ⟨fixes_mul u v⁻¹ p hu (fixes_inv v p hv), hv⟩
  | mulV => exact ⟨hu, fixes_mul v u p hv hu⟩
  | mulVInv => exact ⟨hu, fixes_mul v u⁻¹ p hv (fixes_inv u p hu)⟩
  | conjU c => exact ⟨fixes_conjugate c u p hu hm, hv⟩
  | conjV c => exact ⟨hu, fixes_conjugate c v p hv hm⟩

theorem run_fixes (p : α) (ms : List (Step α)) (s : Pair α)
    (hm : ∀ m ∈ ms, allowedAt p m) (hs : BothFix p s) : BothFix p (run ms s) := by
  induction ms generalizing s with
  | nil => exact hs
  | cons m ms ih =>
      apply ih
      · intro a ha
        exact hm a (List.mem_cons_of_mem m ha)
      · exact step_fixes p m s (hm m (List.mem_cons_self ..)) hs

theorem no_run_eq_of_second_notfix (p : α) (ms : List (Step α)) (s t : Pair α)
    (hm : ∀ m ∈ ms, allowedAt p m) (hs : BothFix p s) (ht : t.2 p ≠ p) :
    run ms s ≠ t := by
  intro h
  have hf := run_fixes p ms s hm hs
  rw [h] at hf
  exact ht hf.2

end Verify.PermutationFixedPointNielsen
