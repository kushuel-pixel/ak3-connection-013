import FixedSCuts

namespace Candidate.AK3Peak.FixedS.StreamCut
open Verify.AtomicSemantics
open Bridge42 (InBall)

abbrev Layers := Nat → WordState → Prop

/-- A layer certificate may safely over-approximate the reachable states. On a
    legal step, the certified layer index can grow by at most one. -/
structure Cover (cap r : Nat) (base : WordState) (layers : Layers) : Prop where
  root : layers 0 base
  step : ∀ i < r, ∀ u, layers i u → ∀ m, total (wordStep m u) ≤ cap →
    ∃ j ≤ i+1, layers j (wordStep m u)

private theorem reaches {cap r : Nat} {base : WordState} {L : Layers} (h : Cover cap r base L)
    (ms : List Move) (hn : ms.length ≤ r) (hp : peak ms base ≤ cap) :
    ∃ i ≤ ms.length, L i (wordRun ms base) := by
  induction ms using List.reverseRecOn with
  | nil => exact ⟨0,le_rfl,h.root⟩
  | append_singleton xs m ih =>
    rw [peak_append] at hp
    rw [run_append]
    have hlen : xs.length < r := by simp at hn; omega
    obtain ⟨i,hi,hu⟩ := ih hlen.le (max_le_iff.mp hp).1
    obtain ⟨j,hj,hv⟩ := h.step i (by omega) _ hu m ((end_le_peak [m] _).trans (max_le_iff.mp hp).2)
    exact ⟨j,by simp; omega,hv⟩

theorem covers_ball {cap r : Nat} {base u : WordState} {L : Layers}
    (h : Cover cap r base L) (hb : InBall cap r base u) : ∃ i ≤ r, L i u := by
  obtain ⟨ms,hlen,he,hp⟩ := hb
  obtain ⟨i,hi,hu⟩ := reaches h ms hlen hp
  exact ⟨i,hi.trans hlen, he ▸ hu⟩

/-- Match the depositor's A-side 16+24 streaming split. The lower 15 A layers
    and 24 S layers require coverage. Only the last stored A layer needs
    an extra move check once the stored balls are disjoint. -/
theorem cap30_from_saved_layers (A S : Layers) (ha : Cover 30 15 ak3 A) (hs : Cover 30 24 source S)
    (stored : ∀ i ≤ 15, ∀ j ≤ 24, ∀ u, A i u → S j u → False)
    (outer : ∀ u, A 15 u → ∀ m, total (wordStep m u) ≤ 30 →
      ∀ j ≤ 24, S j (wordStep m u) → False) : OrdinaryCut 30 16 24 := by
  intro u hu hv
  obtain ⟨j,hj,hv⟩ := covers_ball hs hv
  obtain ⟨ms,hn,he,hp⟩ := hu
  subst u
  by_cases small : ms.length ≤ 15
  · obtain ⟨i,hi,hm⟩ := reaches ha ms small hp
    exact stored i (hi.trans small) j hj _ hm hv
  · cases heq : ms.getLast? with
    | none =>
      have hz := List.getLast?_eq_none_iff.mp heq
      simp [hz] at small
    | some m =>
      obtain ⟨xs,rfl⟩ := List.getLast?_eq_some_iff.mp heq
      have xn : xs.length ≤ 15 := by simp at hn; omega
      rw [peak_append] at hp
      rw [run_append] at hv
      obtain ⟨i,hi,ha'⟩ := reaches ha xs xn (max_le_iff.mp hp).1
      have ht := (end_le_peak [m] _).trans (max_le_iff.mp hp).2
      by_cases last : i = 15
      · subst i
        exact outer _ ha' m ht j hj hv
      · obtain ⟨k,hk,hw⟩ := ha.step i (by omega) _ ha' m ht
        exact stored k (by omega) j hj _ hw hv

end Candidate.AK3Peak.FixedS.StreamCut
