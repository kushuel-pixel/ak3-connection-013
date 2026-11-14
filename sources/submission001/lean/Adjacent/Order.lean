import Adjacent.Family
import Verify.AK3D3RequiredOrder

/-! Pull back the existing fixed-point obstruction from its six-point image
to infinitely many literal targets of the n+8 family. -/
namespace Verify.AdjacentFamily

open AtomicSemantics ResearchWords ROperationConnection
open AK3Mod5FixedPointAdapter AK3SixPointObstruction AK3D3RequiredOrder

private theorem pow_six_residue {G : Type*} [Monoid G] (a : G) (ha : a^6 = 1) (n : ℕ) :
    a^n = a^(n%6) := by
  calc
    a^n = a^(n%6 + 6*(n/6)) := congrArg (fun k : ℕ => a^k) (Nat.mod_add_div n 6).symm
    _ = a^(n%6) := by rw [pow_add, pow_mul, ha, one_pow, mul_one]

/-- This is an exact classification of the image of the second word. -/
theorem target_no_fixed_iff (n : ℕ) :
    (∀ p : Point6, image6 (vFamily n) p ≠ p) ↔ n%6 = 2 ∨ n%6 = 3 ∨ n%6 = 4 := by
  have six : (y6⁻¹)^6 = 1 := by
    apply Equiv.ext
    exact (by decide +kernel : ∀ p : Point6, ((y6⁻¹)^6) p = p)
  have table : ∀ k : Fin 6, (∀ p : Point6, (x6 * (y6⁻¹)^k.val) p ≠ p) ↔
      k.val = 2 ∨ k.val = 3 ∨ k.val = 4 := by decide +kernel
  simp only [vFamily, Y, map_mul, map_pow, map_inv, image6_x, image6_y]
  rw [pow_six_residue _ six n]
  exact table ⟨n%6, Nat.mod_lt _ (by decide)⟩

/-- A successful completed list must contain a y/Y conjugation strictly
before a second-component multiplication (ID4/5). -/
theorem order_to_member (n : ℕ) (ms : List AtomicSemantics.Move)
    (residue : n%6 = 2 ∨ n%6 = 3 ∨ n%6 = 4)
    (ends : groupRun ms originalStart = initial n) : YBeforeSecondMix ms := by
  by_contra hn
  obtain ⟨pre,post,rfl,hpre,hpost⟩ := split_of_no_order ms hn
  have hp := (prefix6_both_fix pre hpre).2
  have fixed := suffix6_second_fixes post (groupRun pre originalStart) hpost 0 hp
  rw [← SevenPrefixUpperBound.groupRun_append, ends] at fixed
  exact (target_no_fixed_iff n).2 residue _ fixed

end Verify.AdjacentFamily
