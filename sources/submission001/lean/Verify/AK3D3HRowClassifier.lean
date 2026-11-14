import Verify.AK3SecondComponentTrace

/-! Classify the 64 chronological two-conjugation choices under the explicit
D3 effective-H condition. This does not derive that condition from an arbitrary
successful original-F path.
-/
namespace Verify.AK3D3HRowClassifier
open Verify.AtomicSemantics
open Verify.AK3Mod5FixedPoint
open Verify.AK3SecondComponentTrace

def conjugationMove (i : Fin 8) : Move :=
  match i.val with
  | 0 => .m6 | 1 => .m7 | 2 => .m8 | 3 => .m9
  | 4 => .m10 | 5 => .m11 | 6 => .m12 | _ => .m13

def conjugationLetter : Move → Verify.F
  | .m6 | .m10 => Verify.x
  | .m7 | .m11 => Verify.X
  | .m8 | .m12 => Verify.y
  | .m9 | .m13 => Verify.Y
  | _ => 1

def targetsSecond : Move → Bool
  | .m10 | .m11 | .m12 | .m13 => true
  | _ => false

def effectiveH (a b : Move) : Verify.F :=
  match targetsSecond a, targetsSecond b with
  | false,false => conjugationLetter b * conjugationLetter a
  | false,true => (conjugationLetter b)⁻¹ * conjugationLetter a
  | true,false => (conjugationLetter a)⁻¹ * conjugationLetter b
  | true,true => (conjugationLetter b * conjugationLetter a)⁻¹

def AllowedD3H (a b : Move) : Prop :=
  effectiveH a b = Verify.Y*Verify.x ∨ effectiveH a b = Verify.X*Verify.y

def positiveRowIndex (i : Fin 8) : Fin 16 :=
  ⟨i.val+8, Nat.add_lt_add_right i.isLt 8⟩

def positiveRowMoves (i : Fin 8) : List Move :=
  match i.val with
  | 0 => [.m6,.m9] | 1 => [.m6,.m12]
  | 2 => [.m8,.m7] | 3 => [.m8,.m10]
  | 4 => [.m10,.m8] | 5 => [.m10,.m13]
  | 6 => [.m12,.m6] | _ => [.m12,.m11]

theorem isConjugation_has_index (m : Move) (hm : isConjugation m = true) :
    ∃ i : Fin 8, conjugationMove i = m := by
  cases m <;> simp [isConjugation] at hm <;> first
  | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩
  | exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩ | exact ⟨7,rfl⟩

theorem allowed_H_finite_table : ∀ i j : Fin 8,
    (effectiveH (conjugationMove i) (conjugationMove j) = Verify.Y*Verify.x ∨
      effectiveH (conjugationMove i) (conjugationMove j) = Verify.X*Verify.y) →
    ∃ k : Fin 8, positiveRowMoves k = [conjugationMove i,conjugationMove j] := by
  decide

theorem allowed_H_has_positive_row (a b : Move)
    (ha : isConjugation a = true) (hb : isConjugation b = true)
    (hH : AllowedD3H a b) : ∃ i : Fin 8, positiveRowMoves i = [a,b] := by
  rcases isConjugation_has_index a ha with ⟨i,rfl⟩
  rcases isConjugation_has_index b hb with ⟨j,rfl⟩
  exact allowed_H_finite_table i j hH

theorem positive_row_negative_false : ∀ i : Fin 8, (row (positiveRowIndex i)).negative = false := by
  decide

theorem positive_row_move_indices : ∀ i : Fin 8,
    (positiveRowMoves i).map Verify.AK3Mod5FixedPointAdapter.moveIndex =
      [(row (positiveRowIndex i)).first,(row (positiveRowIndex i)).second] := by
  decide

end Verify.AK3D3HRowClassifier
