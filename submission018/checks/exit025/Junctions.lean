import Projection
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.Group.Conj

namespace FixedS.Cap28Projection
abbrev Letter := Fin 2 × Bool
def bar (z : Letter) : Letter := (z.1, !z.2)
def product (a b c : Word) : F := FreeGroup.mk a * FreeGroup.mk c * FreeGroup.mk b * (FreeGroup.mk c)⁻¹

/-- These are precisely the four forbidden endpoint equalities for a nonempty
bridge in the pinned checker, expressed without indexing into words. -/
inductive BadJunction : Word → Word → Word → Prop where
  | leftHead (z : Letter) (a b d : Word) : BadJunction (z :: a) b (z :: d)
  | leftLast (z : Letter) (a b d : Word) : BadJunction (a ++ [bar z]) b (z :: d)
  | rightHead (z : Letter) (a b d : Word) : BadJunction a (bar z :: b) (d ++ [z])
  | rightLast (z : Letter) (a b d : Word) : BadJunction a (b ++ [z]) (d ++ [z])

private theorem cons_eval (z : Letter) (a : Word) :
    FreeGroup.mk (z :: a) = FreeGroup.mk [z] * FreeGroup.mk a := rfl

private theorem bar_eval (z : Letter) :
    FreeGroup.mk [bar z] = (FreeGroup.mk [z])⁻¹ := by rw [FreeGroup.inv_mk]; rfl

private theorem drop_left (z : Letter) (a a' b d : Word)
    (h : FreeGroup.mk a' = (FreeGroup.mk [z])⁻¹ * FreeGroup.mk a * FreeGroup.mk [z]) :
    IsConj (product a b (z::d)) (product a' b d) := by
  apply isConj_iff.mpr
  refine ⟨(FreeGroup.mk [z])⁻¹, ?_⟩
  simp only [product, cons_eval z d, h, inv_inv]
  exact slide_left _ _ _ _

private theorem drop_right (z : Letter) (a b b' d : Word)
    (h : FreeGroup.mk b' = FreeGroup.mk [z] * FreeGroup.mk b * (FreeGroup.mk [z])⁻¹) :
    IsConj (product a b (d ++ [z])) (product a b' d) := by
  have e : product a b (d ++ [z]) = product a b' d := by
    simp only [product, ← FreeGroup.mul_mk, h]
    exact slide_right _ _ _ _
  rw [e]

private theorem shrink {a b c : Word} (bad : BadJunction a b c) :
    ∃ a' b' d, List.IsRotated a a' ∧ List.IsRotated b b' ∧ List.IsInfix d c ∧
      d.length < c.length ∧ IsConj (product a b c) (product a' b' d) := by
  cases bad with
  | leftHead z a b d =>
    refine ⟨a ++ [z], b, d, (List.isRotated_concat z a).symm, .refl _, ⟨[z], [], by simp⟩, by simp, drop_left z _ _ _ _ ?_⟩
    rw [cons_eval z a, ← FreeGroup.mul_mk]; group
  | leftLast z a b d =>
    refine ⟨bar z :: a, b, d, List.isRotated_concat _ _, .refl _, ⟨[z], [], by simp⟩, by simp, drop_left z _ _ _ _ ?_⟩
    rw [cons_eval (bar z) a, ← FreeGroup.mul_mk, bar_eval]; group
  | rightHead z a b d =>
    refine ⟨a, b ++ [bar z], d, .refl _, (List.isRotated_concat _ _).symm, ⟨[], [z], by simp⟩, by simp, drop_right z _ _ _ _ ?_⟩
    rw [cons_eval (bar z) b, ← FreeGroup.mul_mk, bar_eval]; group
  | rightLast z a b d =>
    refine ⟨a, z :: b, d, .refl _, List.isRotated_concat _ _, ⟨[], [z], by simp⟩, by simp, drop_right z _ _ _ _ ?_⟩
    rw [cons_eval z b, ← FreeGroup.mul_mk]; group

/-- Rotate the cyclic words and trim only the ends of the bridge until no
junction cancels. An empty result is the checker's separate rotations case. -/
theorem junction_normal_form (a b c : Word) :
    ∃ a' b' d, List.IsRotated a a' ∧ List.IsRotated b b' ∧ List.IsInfix d c ∧
      ¬BadJunction a' b' d ∧ IsConj (product a b c) (product a' b' d) := by
  classical
  by_cases bad : BadJunction a b c
  · obtain ⟨a₁,b₁,d,r₁,r₂,sub,lt,e⟩ := shrink bad
    obtain ⟨a₂,b₂,d₂,s₁,s₂,last,clean,f⟩ := junction_normal_form a₁ b₁ d
    exact ⟨a₂,b₂,d₂,r₁.trans s₁,r₂.trans s₂,last.trans sub,clean,e.trans f⟩
  · exact ⟨a,b,c,.refl _,.refl _,⟨[],[],by simp⟩,bad,.refl _⟩
termination_by c.length

def signedWord (inv : Bool) (w : Word) : Word := if inv then FreeGroup.invRev w else w

/-- The product of two literal relators, with either sign on the multiplier,
has a representative in one of the checker's two junction cases. The theorem
uses the source cap and its cyclic length floor; the output budget, canonical
key implementation and membership of the closed set are audited separately. -/
theorem exact_product_at_28 (r s : Word) (inv : Bool)
    (hcap : r.length + s.length ≤ 28)
    (hmin : 13 ≤ (core r).length + (core s).length) :
    ∃ a b d, List.IsRotated (core r) a ∧ List.IsRotated (signedWord inv (core s)) b ∧
      FreeGroup.IsReduced d ∧ d.length ≤ 7 ∧ ¬BadJunction a b d ∧
      IsConj (FreeGroup.mk r * signed inv (FreeGroup.mk s)) (product a b d) := by
  have hs : FreeGroup.mk (signedWord inv (core s)) = signed inv (FreeGroup.mk (core s)) := by
    cases inv <;> simp [signedWord, signed, FreeGroup.inv_mk]
  have initial : IsConj (FreeGroup.mk r * signed inv (FreeGroup.mk s))
      (product (core r) (signedWord inv (core s)) (bridge r s)) := by
    apply IsConj.symm
    apply isConj_iff.mpr
    exact ⟨FreeGroup.mk (handle r), by rw [product, hs, product_formula r s inv]⟩
  obtain ⟨a,b,d,ra,rb,part,clean,conj⟩ :=
    junction_normal_form (core r) (signedWord inv (core s)) (bridge r s)
  have reduced : FreeGroup.IsReduced (bridge r s) :=
    FreeGroup.IsReduced.of_reduce_eq FreeGroup.reduce.idem
  exact ⟨a,b,d,ra,rb,reduced.infix part,part.length_le.trans (bridge_at_28 r s hcap hmin),
    clean,initial.trans conj⟩

#print axioms exact_product_at_28
#print axioms junction_normal_form
end FixedS.Cap28Projection
