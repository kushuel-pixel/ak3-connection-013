import B5ReverseWitness

namespace Candidate.AK3Peak.Bridge42
open Verify.AtomicSemantics
open Verify.ReducedWords (xLetter XLetter yLetter YLetter)

private def s8 : WordState :=
  ([yLetter, xLetter, yLetter, XLetter, YLetter, XLetter],
   [YLetter, YLetter, xLetter, yLetter, yLetter, yLetter, yLetter, yLetter, XLetter, YLetter, XLetter])

private def s16 : WordState :=
  ([YLetter, YLetter, YLetter, YLetter, XLetter, yLetter, yLetter, yLetter, xLetter],
   [YLetter, xLetter, YLetter, XLetter, YLetter, xLetter, yLetter, yLetter, yLetter])

private def s24 : WordState :=
  ([YLetter, YLetter, YLetter, YLetter, XLetter, yLetter, yLetter, yLetter, xLetter],
   [YLetter, xLetter, YLetter, XLetter, yLetter, yLetter, xLetter])

private def s32 : WordState :=
  ([YLetter, YLetter, YLetter, YLetter, XLetter, yLetter, yLetter, yLetter, xLetter],
   [xLetter, xLetter, YLetter, XLetter, yLetter, yLetter])

private def s40 : WordState :=
  ([yLetter, yLetter, xLetter, YLetter, YLetter, YLetter, YLetter, XLetter, yLetter],
   [xLetter, xLetter, YLetter, YLetter, YLetter, YLetter, YLetter, XLetter, yLetter, yLetter, yLetter, yLetter, yLetter])

private def block0 : List Move := [.m0, .m1, .m12, .m10, .m5, .m13, .m5, .m13]
private theorem step0 : Witness 22 ak3 s8 block0 := by
  unfold Witness
  decide +kernel

private def block8 : List Move := [.m3, .m11, .m4, .m1, .m9, .m7, .m5, .m12]
private theorem step8 : Witness 22 s8 s16 block8 := by
  unfold Witness
  decide +kernel

private def block16 : List Move := [.m12, .m11, .m5, .m12, .m4, .m10, .m12, .m11]
private theorem step16 : Witness 22 s16 s24 block16 := by
  unfold Witness
  decide +kernel

private def block24 : List Move := [.m5, .m12, .m11, .m5, .m12, .m4, .m10, .m12]
private theorem step24 : Witness 22 s24 s32 block24 := by
  unfold Witness
  decide +kernel

private def block32 : List Move := [.m12, .m12, .m6, .m4, .m13, .m13, .m8, .m8]
private theorem step32 : Witness 22 s32 s40 block32 := by
  unfold Witness
  decide +kernel

private def block40 : List Move := [.m8, .m7]
private theorem step40 : Witness 22 s40 source block40 := by
  unfold Witness
  decide +kernel

def forward : List Move :=
  (block0 ++ (block8 ++ (block16 ++ (block24 ++ (block32 ++ block40)))))

theorem forward_ok : Witness 22 ak3 source forward :=
  (witness_append step0 (witness_append step8 (witness_append step16 (witness_append step24 (witness_append step32 step40)))))

private theorem start_reduced : ReducedState ak3 := by
  constructor <;> apply FreeGroup.IsReduced.of_reduce_eq <;> decide +kernel

def backward : List Move := reverseMoves forward

theorem backward_ok : Witness 22 source ak3 backward :=
  witness_reverse start_reduced forward_ok

theorem lengths : forward.length = 42 ∧ backward.length = 42 := by decide +kernel

theorem peaks : peak forward ak3 = 22 ∧ peak backward source = 22 := by
  have hend := end_le_peak forward ak3
  rw [forward_ok.1] at hend
  exact ⟨le_antisymm forward_ok.2 hend, le_antisymm backward_ok.2 (source_le_peak backward source)⟩

/-- Cap-bounded reachability in at most r moves, including the starting state. -/
def InBall (cap r : ℕ) (s u : WordState) : Prop :=
  ∃ ms : List Move, ms.length ≤ r ∧ Witness cap s u ms

private theorem reverse_length (ms : List Move) : (reverseMoves ms).length = ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [reverseMoves, ih]

/-- Any short witness has a meeting point in the two closed balls. -/
theorem witness_split {cap p q : ℕ} {s t : WordState} {ms : List Move}
    (hs : ReducedState s) (w : Witness cap s t ms) (hlen : ms.length ≤ p + q) :
    ∃ u, InBall cap p s u ∧ InBall cap q t u := by
  let xs := ms.take p
  let ys := ms.drop p
  have hxy : xs ++ ys = ms := List.take_append_drop p ms
  obtain ⟨he, hb⟩ := w
  rw [← hxy, run_append] at he
  rw [← hxy, peak_append] at hb
  obtain ⟨hx, hy⟩ := max_le_iff.mp hb
  have tailW : Witness cap (wordRun xs s) t ys := ⟨he, hy⟩
  refine ⟨wordRun xs s, ⟨xs, ?_, rfl, hx⟩,
    ⟨reverseMoves ys, ?_, witness_reverse (wordRun_reduced xs s hs) tailW⟩⟩
  · simp [xs]
  · rw [reverse_length]
    simp only [ys, List.length_drop]
    omega

/-- The remaining input for minimality is disjointness of the actual bounded balls. -/
theorem shortest_of_disjoint
    (h : ∀ u, InBall 22 16 ak3 u → InBall 22 25 source u → False) :
    (∃ ms : List Move, ms.length = 42 ∧ Witness 22 ak3 source ms) ∧
    (∀ ms : List Move, Witness 22 ak3 source ms → 42 ≤ ms.length) := by
  refine ⟨⟨forward, lengths.1, forward_ok⟩, ?_⟩
  intro ms w
  by_contra! hshort
  have bound : ms.length ≤ 16 + 25 := by omega
  obtain ⟨u, ha, hb⟩ := witness_split start_reduced w bound
  exact h u ha hb

end Candidate.AK3Peak.Bridge42
#check Candidate.AK3Peak.Bridge42.forward_ok
#print axioms Candidate.AK3Peak.Bridge42.forward_ok
#check Candidate.AK3Peak.Bridge42.backward_ok
#print axioms Candidate.AK3Peak.Bridge42.backward_ok
#check Candidate.AK3Peak.Bridge42.lengths
#print axioms Candidate.AK3Peak.Bridge42.lengths
#check Candidate.AK3Peak.Bridge42.peaks
#print axioms Candidate.AK3Peak.Bridge42.peaks
#check Candidate.AK3Peak.Bridge42.witness_split
#print axioms Candidate.AK3Peak.Bridge42.witness_split
#check Candidate.AK3Peak.Bridge42.shortest_of_disjoint
#print axioms Candidate.AK3Peak.Bridge42.shortest_of_disjoint
