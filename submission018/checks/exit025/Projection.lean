import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Tactic.Group

namespace FixedS.Cap28Projection

abbrev Word := List (Fin 2 × Bool)
abbrev F := FreeGroup (Fin 2)
abbrev core (w : Word) := FreeGroup.reduceCyclically w
abbrev handle (w : Word) := FreeGroup.reduceCyclically.conjugator w

/-- The reduced relative conjugator used when the two relators are multiplied. -/
def bridge (r s : Word) : Word :=
  FreeGroup.reduce (FreeGroup.invRev (handle r) ++ handle s)

theorem length_split (w : Word) :
    w.length = (core w).length + 2 * (handle w).length := by
  have h := congrArg List.length
    (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically w)
  simp only [List.length_append, FreeGroup.invRev_length] at h
  change w.length = (FreeGroup.reduceCyclically w).length + 2 * (FreeGroup.reduceCyclically.conjugator w).length
  omega

theorem bridge_bound (r s : Word) :
    2 * (bridge r s).length + (core r).length + (core s).length ≤
      r.length + s.length := by
  have h : (bridge r s).length ≤ (FreeGroup.invRev (handle r) ++ handle s).length :=
    FreeGroup.Red.length_le FreeGroup.reduce.red
  simp at h
  have hr := length_split r
  have hs := length_split s
  omega

theorem bridge_at_28 (r s : Word) (cap : r.length + s.length ≤ 28)
    (minimum : 13 ≤ (core r).length + (core s).length) : (bridge r s).length ≤ 7 := by
  have := bridge_bound r s
  omega

private theorem eval_split (r : Word) :
    FreeGroup.mk r = FreeGroup.mk (handle r) * FreeGroup.mk (core r) * (FreeGroup.mk (handle r))⁻¹ := by
  rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk]
  exact (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically r).symm ▸ rfl

private theorem eval_bridge (r s : Word) :
    FreeGroup.mk (bridge r s) = (FreeGroup.mk (handle r))⁻¹ * FreeGroup.mk (handle s) := by
  rw [bridge, FreeGroup.reduce.self, FreeGroup.inv_mk, FreeGroup.mul_mk]

def signed (b : Bool) (g : F) : F := if b then g⁻¹ else g

/-- Both signs of right multiplication, with either choice of the relator r.
The determinant and finite quotient checks are separate from this identity. -/
theorem product_formula (r s : Word) (b : Bool) :
    FreeGroup.mk r * signed b (FreeGroup.mk s) =
      FreeGroup.mk (handle r) *
        (FreeGroup.mk (core r) * FreeGroup.mk (bridge r s) *
          signed b (FreeGroup.mk (core s)) * (FreeGroup.mk (bridge r s))⁻¹) *
        (FreeGroup.mk (handle r))⁻¹ := by
  rw [eval_bridge]
  conv_lhs => rw [eval_split r, eval_split s]
  cases b <;> simp only [signed, Bool.false_eq_true, ite_false, ite_true] <;> group

/-- Removing the first bridge letter conjugates the first cyclic word. -/
theorem slide_left (a b z d : F) :
    z⁻¹ * (a * (z*d) * b * (z*d)⁻¹) * z =
      (z⁻¹*a*z) * d * b * d⁻¹ := by group

/-- Removing the last bridge letter conjugates the second cyclic word. -/
theorem slide_right (a b z d : F) :
    a * (d*z) * b * (d*z)⁻¹ = a * d * (z*b*z⁻¹) * d⁻¹ := by group

#print axioms bridge_bound
#print axioms bridge_at_28
#print axioms product_formula
#print axioms slide_left
#print axioms slide_right

end FixedS.Cap28Projection
