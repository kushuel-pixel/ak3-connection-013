import Verify.AK3D3HRowClassifier

/-! Construct the previously explicit hrow argument from an actual tail trace
and its effective-H restriction. All required structural hypotheses are stated.
-/
namespace Verify.AK3D3HRowConnection
open Verify.AtomicSemantics
open Verify.PermutationFixedPointNielsen
open Verify.AK3Mod5FixedPoint
open Verify.AK3Mod5FixedPointAdapter
open Verify.AK3SecondComponentTrace
open Verify.AK3D3HRowClassifier

def D3 : GroupState := (originalR,originalT false)

theorem positive_row_second_image (i : Fin 8) :
    image ((groupRun (positiveRowMoves i) D3).2) = rowSecond (positiveRowIndex i) := by
  have hs : imagePair D3 = (1,t5 false) := by
    apply Prod.ext
    · exact image_R.trans r5_eq_one
    · exact image_T false
  change (imagePair (groupRun (positiveRowMoves i) D3)).2 = _
  rw [image_run14, positive_row_move_indices, hs]
  simp only [run14, List.map_cons, List.map_nil, run, rowSecond,
    positive_row_negative_false]

theorem hrow_of_positive_trace (qs : List Move) (i : Fin 8)
    (hn : NoSecondMix qs) (ht : conjugationTrace qs = positiveRowMoves i) :
    image ((groupRun qs D3).2) = signedRowSecond (positiveRowIndex i) (secondNegative qs) := by
  rw [groupRun_second_trace qs D3 hn, ht]
  cases hb : secondNegative qs <;>
    simp [signed, signedRowSecond, map_inv, positive_row_second_image]

theorem hrow_of_tail_constraints (qs : List Move) (a b : Move)
    (hn : NoSecondMix qs) (ht : conjugationTrace qs = [a,b])
    (hH : AllowedD3H a b) :
    ∃ i : Fin 8, image ((groupRun qs D3).2) =
      signedRowSecond (positiveRowIndex i) (secondNegative qs) := by
  have ha : isConjugation a = true := by
    have hm : a ∈ conjugationTrace qs := by rw [ht]; simp
    exact (List.mem_filter.mp hm).2
  have hb : isConjugation b = true := by
    have hm : b ∈ conjugationTrace qs := by rw [ht]; simp
    exact (List.mem_filter.mp hm).2
  rcases allowed_H_has_positive_row a b ha hb hH with ⟨i,hi⟩
  exact ⟨i,hrow_of_positive_trace qs i hn (ht.trans hi.symm)⟩

def XConjugation (m : Move) : Prop := m = .m6 ∨ m = .m7 ∨ m = .m10 ∨ m = .m11

def XOnlyTrace (ms : List Move) : Prop := ∀ m ∈ conjugationTrace ms, XConjugation m

theorem safe_of_not_conjugation (m : Move) (hc : isConjugation m = false) :
    SafeId (moveIndex m) := by
  cases m <;> simp [isConjugation] at hc <;>
    simp only [SafeId, moveIndex, moveId] <;> decide

theorem safe_of_x_conjugation (m : Move) (hx : XConjugation m) :
    SafeId (moveIndex m) := by
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp only [SafeId, moveIndex, moveId] <;> decide

theorem safeMoves_of_x_only_trace (ms : List Move) (hx : XOnlyTrace ms) : SafeMoves ms := by
  intro m hm
  cases hc : isConjugation m with
  | false => exact safe_of_not_conjugation m hc
  | true => exact safe_of_x_conjugation m (hx m (List.mem_filter.mpr ⟨hm,hc⟩))

theorem no_boundary_of_positive_trace (ms qs : List Move) (i : Fin 8)
    (hx : XOnlyTrace ms) (hn : NoSecondMix qs)
    (ht : conjugationTrace qs = positiveRowMoves i) :
    groupRun ms originalStart ≠ groupRun qs D3 := by
  have hi := hrow_of_positive_trace qs i hn ht
  have hrow : image ((groupRun qs (originalR,originalT (row (positiveRowIndex i)).negative)).2) =
      signedRowSecond (positiveRowIndex i) (secondNegative qs) := by
    simpa only [positive_row_negative_false, D3] using hi
  simpa only [positive_row_negative_false, D3] using
    no_original_row_boundary ms qs (safeMoves_of_x_only_trace ms hx)
      (positiveRowIndex i) (secondNegative qs) hrow

theorem no_boundary_of_tail_constraints (ms qs : List Move) (a b : Move)
    (hx : XOnlyTrace ms) (hn : NoSecondMix qs)
    (ht : conjugationTrace qs = [a,b]) (hH : AllowedD3H a b) :
    groupRun ms originalStart ≠ groupRun qs D3 := by
  rcases hrow_of_tail_constraints qs a b hn ht hH with ⟨i,hi⟩
  have hrow : image ((groupRun qs (originalR,originalT (row (positiveRowIndex i)).negative)).2) =
      signedRowSecond (positiveRowIndex i) (secondNegative qs) := by
    simpa only [positive_row_negative_false, D3] using hi
  simpa only [positive_row_negative_false, D3] using
    no_original_row_boundary ms qs (safeMoves_of_x_only_trace ms hx)
      (positiveRowIndex i) (secondNegative qs) hrow

end Verify.AK3D3HRowConnection
