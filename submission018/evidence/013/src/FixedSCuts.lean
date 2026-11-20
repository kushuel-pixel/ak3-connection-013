import FixedSPaths
namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics
open Bridge42 (InBall)

theorem start_reduced : ReducedState ak3 := by
  constructor <;> apply FreeGroup.IsReduced.of_reduce_eq <;> decide +kernel

theorem allowed_symm (s t : WordState) : allowed s t = allowed t s := by
  cases hs : (s == U) <;> cases ht : (s == V) <;> cases hu : (t == U) <;>
    cases hv : (t == V) <;> simp [allowed, hs, ht, hu, hv]

theorem avoids_append (xs ys : List Move) (s : WordState) :
    avoids (xs ++ ys) s = (avoids xs s && avoids ys (wordRun xs s)) := by
  induction xs generalizing s with
  | nil => rfl
  | cons m ms ih => simp only [List.cons_append, avoids, wordRun, ih, Bool.and_assoc]

theorem avoids_reverse {s : WordState} {ms : List Move} (hr : ReducedState s)
    (ha : avoids ms s = true) : avoids (reverseMoves ms) (wordRun ms s) = true := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
    rw [reverseMoves, avoids_append]
    simp only [avoids, Bool.and_eq_true] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have ht := wordStep_reduced m s hr
    have hw : Witness (peak ms (wordStep m s)) (wordStep m s) (wordRun ms (wordStep m s)) ms :=
      ⟨rfl, le_rfl⟩
    change (avoids (reverseMoves ms) (wordRun ms (wordStep m s)) &&
      avoids [inverseAtom m] (wordRun (reverseMoves ms) (wordRun ms (wordStep m s)))) = true
    rw [ih ht ha2, (witness_reverse ht hw).1]
    simpa only [avoids, Bool.true_and, Bool.and_true, undo_word_step m s hr, allowed_symm (wordStep m s) s]
      using ha1

def AvoidBall (cap r : Nat) (s t : WordState) : Prop :=
  ∃ ms : List Move, ms.length ≤ r ∧ AvoidWitness cap s t ms

theorem avoid_split {cap p q : Nat} {s t : WordState} {ms : List Move} (hs : ReducedState s)
    (w : AvoidWitness cap s t ms) (hlen : ms.length ≤ p + q) :
    ∃ u, AvoidBall cap p s u ∧ AvoidBall cap q t u := by
  let xs := ms.take p
  let ys := ms.drop p
  have hxy : xs ++ ys = ms := List.take_append_drop p ms
  obtain ⟨⟨he,hp⟩,ha⟩ := w
  rw [← hxy, run_append] at he
  rw [← hxy, peak_append] at hp
  rw [← hxy, avoids_append, Bool.and_eq_true] at ha
  obtain ⟨hx,hy⟩ := max_le_iff.mp hp
  have tailW : Witness cap (wordRun xs s) t ys := ⟨he,hy⟩
  refine ⟨wordRun xs s, ⟨xs, by simp [xs], ⟨rfl,hx⟩,ha.1⟩,
    ⟨reverseMoves ys, ?_, witness_reverse (wordRun_reduced xs s hs) tailW, ?_⟩⟩
  · have lenRev (zs : List Move) : (reverseMoves zs).length = zs.length := by
      induction zs with
      | nil => rfl
      | cons m zs ih => simp [reverseMoves, ih]
    rw [lenRev]
    simp only [ys, List.length_drop]
    omega
  · rw [← he]
    exact avoids_reverse (wordRun_reduced xs s hs) ha.2

def OrdinaryCut (h r t : Nat) : Prop :=
  ∀ u, InBall h r ak3 u → InBall h t source u → False
def DeletedCut (h r t : Nat) : Prop :=
  ∀ u, AvoidBall h r ak3 u → AvoidBall h t source u → False

theorem lower_of_cut {cap r t : Nat} (h : OrdinaryCut cap r t)
    {ms : List Move} (w : Witness cap ak3 source ms) : r+t < ms.length := by
  by_contra! hshort
  obtain ⟨u,ha,hb⟩ := Bridge42.witness_split start_reduced w hshort
  exact h u ha hb

theorem lower_of_deleted_cut {cap r t : Nat} (h : DeletedCut cap r t)
    {ms : List Move} (w : AvoidWitness cap ak3 source ms) : r+t < ms.length := by
  by_contra! hshort
  obtain ⟨u,ha,hb⟩ := avoid_split start_reduced w hshort
  exact h u ha hb

def Exact (ok : List Move → Prop) (d : Nat) : Prop :=
  (∃ ms, ms.length = d ∧ ok ms) ∧ ∀ ms, ok ms → d ≤ ms.length

theorem deleted22_of_cut (h : DeletedCut 22 17 26) :
    Exact (AvoidWitness 22 ak3 source) 44 :=
  ⟨⟨bypass22, bypass22_ok.1, bypass22_ok.2.2⟩, fun _ w => lower_of_deleted_cut h w⟩

/-- All integer caps in the proposed table follow from these three finite cuts. -/
theorem distance_table_of_cuts (h22 : DeletedCut 22 17 26) (h24 : OrdinaryCut 24 15 26)
    (h30 : OrdinaryCut 30 16 24) :
    (Exact (Witness 22 ak3 source) 42 ∧ Exact (AvoidWitness 22 ak3 source) 44) ∧
    (∀ h, 23 ≤ h → h ≤ 24 → Exact (Witness h ak3 source) 42 ∧ Exact (AvoidWitness h ak3 source) 42) ∧
    (∀ h, 25 ≤ h → h ≤ 30 → Exact (Witness h ak3 source) 41 ∧ Exact (AvoidWitness h ak3 source) 41) := by
  have widen {h k : Nat} {ms : List Move} (hk : h ≤ k) (w : Witness h ak3 source ms) :
      Witness k ak3 source ms := ⟨w.1, w.2.trans hk⟩
  have both {h k top d r t : Nat} {ms : List Move} (hk : h ≤ k) (kt : k ≤ top)
      (w : AvoidWitness h ak3 source ms) (len : ms.length = d)
      (neg : OrdinaryCut top r t) (eq : r+t+1 = d) :
      Exact (Witness k ak3 source) d ∧ Exact (AvoidWitness k ak3 source) d := by
    have low (ys) (wy : Witness k ak3 source ys) : d ≤ ys.length := by
      have := lower_of_cut neg (widen kt wy)
      omega
    exact ⟨⟨⟨ms,len,widen hk w.1⟩,low⟩,
      ⟨⟨ms,len,widen hk w.1,w.2⟩,fun ys hys => low ys hys.1⟩⟩
  refine ⟨⟨⟨⟨Bridge42.forward,Bridge42.lengths.1,Bridge42.forward_ok⟩,?_⟩,
    deleted22_of_cut h22⟩, ?_, ?_⟩
  · intro ms w
    exact lower_of_cut h24 (widen (by decide) w)
  · intro h hh hk
    exact both hh hk bypass23_ok.2.2 bypass23_ok.1 h24 rfl
  · intro h hh hk
    exact both hh hk bypass25_ok.2.2 bypass25_ok.1 h30 rfl

end Candidate.AK3Peak.FixedS
