import PairedPaths

namespace Candidate.AK3Peak.FixedS.RecordedPeak29
open Verify.AtomicSemantics

/-- A chronological prefix visits the prescribed successive layers within the cap. -/
private def prefixOK (cap : Nat) : List Move → List (List WordState) → WordState → Bool
  | [], [], _ => true
  | m :: ms, layer :: rest, s =>
    decide (total s ≤ cap) && decide (wordStep m s ∈ layer) && prefixOK cap ms rest (wordStep m s)
  | _, _, _ => false

private theorem append_mem {cap : Nat} (xs : List Move) (front : List (List WordState))
    (rest : List (List WordState)) (s : WordState) (ys : List Move)
    (hp : prefixOK cap xs front s = true)
    (hy : ys ∈ listsOn cap rest (wordRun xs s)) :
    xs ++ ys ∈ listsOn cap (front ++ rest) s := by
  induction xs generalizing front s with
  | nil =>
    cases front <;> simp_all [prefixOK, wordRun]
  | cons m ms ih =>
    cases front with
    | nil => simp [prefixOK] at hp
    | cons layer layers =>
      simp only [prefixOK, Bool.and_eq_true, decide_eq_true_eq] at hp
      obtain ⟨⟨hc,hv⟩,tailOK⟩ := hp
      have tail := ih layers (wordStep m s) tailOK hy
      simp only [List.cons_append,listsOn,ite_eq_left hc,List.mem_flatMap]
      refine ⟨m,labels_complete m,?_⟩
      simpa [hv] using (List.mem_map_of_mem (f := (m :: ·)) tail)

abbrev highPrefix := firstTwo ++ arm29
abbrev lowPrefix := firstTwo ++ arm27
def tails := listsOn 27 suffixLayers joinState
def all29 := listsOn 29 recordedLayers ak3
def extra := all29.filter (fun ms => !decide (peak ms ak3 ≤ 28))

private theorem extra_length : extra.length = 34624 := by
  let low (ms : List Move) := decide (peak ms ak3 ≤ 28)
  have h : (all29.filter low).Perm (listsOn 28 recordedLayers ak3) := by
    apply (List.perm_ext_iff_of_nodup ((listsOn_nodup _ _ _).filter _) (listsOn_nodup _ _ _)).mpr
    intro ms
    simp only [List.mem_filter,low,decide_eq_true_eq]
    exact (monotone_membership (by decide : 28 ≤ 29) _ _ _).symm
  have H := h.length_eq.trans ((listsOn_length _ _ _).trans recorded_counts.1)
  have N : all29.length = 106036 := (listsOn_length _ _ _).trans recorded_counts.2
  have sum := List.length_eq_length_filter_add (l := all29) low
  change all29.length = _ + extra.length at sum
  omega

private theorem generated_mem (ys : List Move) (hy : ys ∈ tails) : highPrefix ++ ys ∈ extra := by
  have endP : wordRun highPrefix ak3 = joinState := by decide +kernel
  have p : prefixOK 29 highPrefix (recordedLayers.take 7) ak3 = true := by decide +kernel
  have hy29 := ((monotone_membership (by decide : 27 ≤ 29) suffixLayers joinState ys).mp hy).1
  rw [← endP] at hy29
  have hm := append_mem highPrefix (recordedLayers.take 7) suffixLayers ak3 ys p hy29
  have splitLayers : recordedLayers.take 7 ++ suffixLayers = recordedLayers := rfl
  rw [splitLayers] at hm
  have peakP : peak highPrefix ak3 = 29 := by decide +kernel
  apply List.mem_filter.mpr
  refine ⟨hm, ?_⟩
  rw [peak_append highPrefix ys ak3, peakP]
  simp

private theorem perm_from_size {α : Type*} {a b : List α} (nd : a.Nodup)
    (sub : a ⊆ b) (sz : a.length = b.length) : a.Perm b := by
  obtain ⟨v,p,h⟩ := List.subperm_of_subset nd sub
  have e : v = b := h.eq_of_length (p.length_eq.trans sz)
  exact e ▸ p.symm

/-- In the deposited layers the extra cap-29 paths are exactly the high prefix
    attached to the cap-27 suffixes. A permutation identifies lists up to order. -/
theorem all_extra_are_high_prefix :
    (tails.map (fun ys => highPrefix ++ ys)).Perm extra := by
  have nd : (tails.map (fun ys => highPrefix ++ ys)).Nodup :=
    (listsOn_nodup _ _ _).map (fun _ _ h => List.append_cancel_left h)
  have sub : tails.map (fun ys => highPrefix ++ ys) ⊆ extra := by
    intro ms h
    obtain ⟨ys,hm,rfl⟩ := List.mem_map.mp h
    exact generated_mem ys hm
  have lenT : tails.length = 34624 := (listsOn_length _ _ _).trans shared_suffix_count
  have eqLen : (tails.map (fun ys => highPrefix ++ ys)).length = extra.length := by
    simp [extra_length,lenT]
  exact perm_from_size nd sub eqLen

/-- Replacing the five-move arm in each extra path gives a recorded cap-27 path
    with the same suffix. -/
theorem low_companion (ys : List Move) (hy : ys ∈ tails) :
    lowPrefix ++ ys ∈ listsOn 27 recordedLayers ak3 := by
  have he : wordRun lowPrefix ak3 = joinState := by decide +kernel
  have hp : prefixOK 27 lowPrefix (recordedLayers.take 7) ak3 = true := by decide +kernel
  have ht : ys ∈ listsOn 27 suffixLayers (wordRun lowPrefix ak3) := by rw [he]; exact hy
  exact append_mem lowPrefix (recordedLayers.take 7) suffixLayers ak3 ys hp ht

/-- A recorded sequence newly admitted at 29 has one and only one suffix in
    the specified cap-27 suffix layers after the fixed high prefix. -/
theorem new_at_29_iff (ms : List Move) :
    (ms ∈ listsOn 29 recordedLayers ak3 ∧ ms ∉ listsOn 28 recordedLayers ak3) ↔
    ∃! ys, ys ∈ tails ∧ ms = highPrefix ++ ys := by
  have monotone := monotone_membership (by decide : 28 ≤ 29) recordedLayers ak3 ms
  have classified : ms ∈ extra ↔
      ms ∈ listsOn 29 recordedLayers ak3 ∧ ms ∉ listsOn 28 recordedLayers ak3 := by
    simp only [extra, all29, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro ⟨hm, hp⟩
      exact ⟨hm, fun h28 => hp (monotone.mp h28).2⟩
    · rintro ⟨hm,h28⟩
      exact ⟨hm, fun hp => h28 (monotone.mpr ⟨hm,hp⟩)⟩
  rw [← classified, ← all_extra_are_high_prefix.mem_iff]
  constructor
  · intro h
    obtain ⟨ys, hy, he⟩ := List.mem_map.mp h
    refine ⟨ys, ⟨hy, he.symm⟩, ?_⟩
    intro other ho
    exact List.append_cancel_left (ho.2.symm.trans he.symm)
  · rintro ⟨ys, ⟨hy, he⟩, _⟩
    exact List.mem_map.mpr ⟨ys, hy, he.symm⟩

#print axioms new_at_29_iff
#print axioms all_extra_are_high_prefix
#print axioms low_companion
end Candidate.AK3Peak.FixedS.RecordedPeak29
