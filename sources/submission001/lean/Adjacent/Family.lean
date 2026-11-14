import Verify.SevenPrefix

/-! Adjacent members of the n+8 family in the original, ordered ac-r2-v1 model. -/
namespace Verify.AdjacentFamily

open AtomicSemantics ResearchWords ROperationConnection
open SevenPrefixUpperBound (canonicalInitial)

/-- The two ways of multiplying by a conjugate agree in every group. -/
theorem conjugated_mul_pair {G : Type*} [Group G] (g h w : G) :
    (g * ((g⁻¹ * h * g) * w) * g⁻¹, w) =
      (h * (g * w * g⁻¹), g⁻¹ * (g * w * g⁻¹) * g) := by
  apply Prod.ext <;> simp [mul_assoc]

/-- Specialize the group identity to two literal lists in the existing evaluator. -/
theorem three_runs_eq (s : GroupState) :
    groupRun [.m9,.m2,.m8] s = groupRun [.m12,.m2,.m13] s := by
  rcases s with ⟨h,w⟩
  exact conjugated_mul_pair y h w

theorem three_value (h w : F) :
    groupRun [.m9,.m2,.m8] (h,w) = (h * (y * w * Y),w) := by
  rw [three_runs_eq]
  apply Prod.ext <;> simp [groupRun, groupStep, Y, mul_assoc]

theorem advance_second (n : ℕ) :
    groupRun [.m11,.m4] (initial n) = (uFamily n, vFamily (n+1)) := by
  apply Prod.ext <;>
    simp [groupRun, groupStep, initial, uFamily, vFamily, X, Y, mul_assoc]

private theorem cancel_new_second (n : ℕ) :
    uFamily n * (vFamily (n+1))⁻¹ = X * y^n := by
  simp [uFamily, vFamily, X, Y, mul_assoc]

theorem adjacent_via_first (n : ℕ) :
    groupRun [.m11,.m4,.m3,.m9,.m2,.m8] (initial n) = initial (n+1) := by
  change groupRun [.m3,.m9,.m2,.m8] (groupRun [.m11,.m4] (initial n)) = _
  rw [advance_second]
  change groupRun [.m9,.m2,.m8] (uFamily n * (vFamily (n+1))⁻¹, vFamily (n+1)) = _
  rw [three_value, cancel_new_second]
  apply Prod.ext
  · change X * y^n * (y * (x * Y^(n+1)) * Y) = X * y^(n+1) * x * Y^((n+1)+1)
    rw [pow_succ y n, pow_succ Y (n+1)]
    simp only [mul_assoc]
  · rfl

theorem adjacent_via_second (n : ℕ) :
    groupRun [.m11,.m4,.m3,.m12,.m2,.m13] (initial n) = initial (n+1) := by
  change groupRun [.m12,.m2,.m13] (groupRun [.m11,.m4,.m3] (initial n)) = _
  rw [← three_runs_eq]
  exact adjacent_via_first n

/-- Transfer any established group-level route to literal reduced words. -/
theorem canonical_transfer (ms : List AtomicSemantics.Move) (n k : ℕ)
    (ends : groupRun ms (initial n) = initial k) :
    wordRun ms (canonicalInitial n) = canonicalInitial k := by
  rw [wordRun_canonical _ _ (SevenPrefixUpperBound.canonicalInitial_reduced n),
    SevenPrefixUpperBound.eval_canonicalInitial, ends]
  rfl

/-- Include step zero and the last state. Each entry is the sum of both word lengths. -/
def lengthTrace (ms : List AtomicSemantics.Move) (start : WordState) : List ℕ :=
  (List.range (ms.length+1)).map fun k =>
    let w := wordRun (ms.take k) start
    w.1.length + w.2.length

theorem d3_first_trace :
    lengthTrace [.m11,.m4,.m3,.m9,.m2,.m8] (canonicalInitial 3) =
      [13,13,14,9,11,16,16] := by decide +kernel

theorem d3_second_trace :
    lengthTrace [.m11,.m4,.m3,.m12,.m2,.m13] (canonicalInitial 3) =
      [13,13,14,9,11,18,16] := by decide +kernel

end Verify.AdjacentFamily
