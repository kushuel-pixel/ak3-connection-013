import Verify.AK3Mod5FixedPointAdapter

/-! Exact second-component semantics for intervals with no IDs4/5.
Arbitrary IDs0..3 are allowed. Conjugation order is preserved, while IDs1
contribute only one overall inverse sign. No length bound is imposed.
-/
namespace Verify.AK3SecondComponentTrace
open Verify.AtomicSemantics

def isConjugation : Move → Bool
  | .m6 | .m7 | .m8 | .m9 | .m10 | .m11 | .m12 | .m13 => true
  | _ => false

def conjugationTrace (ms : List Move) : List Move := ms.filter isConjugation

def NoSecondMix (ms : List Move) : Prop := ∀ m ∈ ms, m ≠ .m4 ∧ m ≠ .m5

def secondLetter : Move → Verify.F
  | .m10 => Verify.x | .m11 => Verify.X
  | .m12 => Verify.y | .m13 => Verify.Y
  | _ => 1

def secondConjugator : List Move → Verify.F
  | [] => 1
  | m::ms => secondConjugator ms * secondLetter m

def secondNegative : List Move → Bool
  | [] => false
  | .m1::ms => !(secondNegative ms)
  | _::ms => secondNegative ms

def signed (negative : Bool) (v : Verify.F) : Verify.F := if negative then v⁻¹ else v

theorem signed_conjugate (negative : Bool) (c v : Verify.F) :
    signed negative (c*v*c⁻¹) = c * signed negative v * c⁻¹ := by
  cases negative <;> simp [signed, mul_inv_rev, mul_assoc]

theorem secondConjugator_trace (ms : List Move) :
    secondConjugator ms = secondConjugator (conjugationTrace ms) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      cases m <;> simp [conjugationTrace, List.filter_cons, isConjugation,
        secondConjugator, secondLetter, ih]

theorem trace_no_second_mix (ms : List Move) : NoSecondMix (conjugationTrace ms) := by
  intro m hm
  have hc := (List.mem_filter.mp hm).2
  cases m <;> simp_all [isConjugation]

theorem trace_secondNegative (ms : List Move) : secondNegative (conjugationTrace ms) = false := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      cases m <;> simpa [conjugationTrace, List.filter_cons, isConjugation, secondNegative] using ih

theorem groupRun_second_form (ms : List Move) (s : GroupState) (hn : NoSecondMix ms) :
    (groupRun ms s).2 =
      secondConjugator ms * signed (secondNegative ms) s.2 * (secondConjugator ms)⁻¹ := by
  induction ms generalizing s with
  | nil => simp [groupRun, secondConjugator, secondNegative, signed]
  | cons m ms ih =>
      have ht : NoSecondMix ms := by
        intro a ha
        exact hn a (List.mem_cons_of_mem m ha)
      have hh := hn m (List.mem_cons_self ..)
      rw [groupRun, ih (groupStep m s) ht]
      cases m <;> first
      | exact False.elim (hh.1 rfl)
      | exact False.elim (hh.2 rfl)
      | cases hb : secondNegative ms <;>
          simp [secondConjugator, secondLetter, secondNegative, groupStep,
            hb, signed, Verify.X, Verify.Y, mul_inv_rev, mul_assoc]

theorem groupRun_second_trace (ms : List Move) (s : GroupState) (hn : NoSecondMix ms) :
    (groupRun ms s).2 =
      signed (secondNegative ms) ((groupRun (conjugationTrace ms) s).2) := by
  have ht := groupRun_second_form (conjugationTrace ms) s (trace_no_second_mix ms)
  rw [trace_secondNegative] at ht
  simp only [signed, Bool.false_eq_true, ite_false] at ht
  rw [groupRun_second_form ms s hn, ht, ← secondConjugator_trace ms, signed_conjugate]

end Verify.AK3SecondComponentTrace
