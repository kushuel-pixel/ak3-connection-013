import RecordedCounts

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

/-- Explicit ordered move lists for the layer-constrained search. -/
def listsOn (cap : Nat) : List (List WordState) → WordState → List (List Move)
  | [], s => if total s ≤ cap ∧ s = source then [[]] else []
  | layer::layers, s =>
    if total s ≤ cap then labels.flatMap (fun m => let v := wordStep m s
      if v ∈ layer then (listsOn cap layers v).map (m :: ·) else []) else []

theorem listsOn_length (cap : Nat) (layers : List (List WordState)) (s : WordState) :
    (listsOn cap layers s).length = countFrom cap layers s := by
  induction layers generalizing s with
  | nil => simp only [listsOn, countFrom]; split <;> rfl
  | cons layer layers ih =>
    simp only [listsOn,countFrom]
    split <;> try rfl
    simp only [List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro m _
    split <;> simp [ih]

private theorem labelled_nodup (f : Move → List (List Move))
    (hf : ∀ m, (f m).Nodup) :
    (labels.flatMap (fun m => (f m).map (m :: ·))).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro m _
    apply (hf m).map
    intro a b h
    exact (List.cons.inj h).2
  · apply labels_distinct.imp
    intro m n hmn
    apply List.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,_,ha⟩ := List.mem_map.mp hx
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hy
    exact hmn (List.cons.inj (ha.trans hb.symm)).1

theorem listsOn_nodup (cap : Nat) (layers : List (List WordState)) (s : WordState) :
    (listsOn cap layers s).Nodup := by
  induction layers generalizing s with
  | nil => simp only [listsOn]; split <;> simp
  | cons layer layers ih =>
    rw [listsOn]
    split
    · let f (m : Move) := if wordStep m s ∈ layer then listsOn cap layers (wordStep m s) else []
      have hh (m : Move) : (f m).Nodup := by unfold f; split <;> simp [ih]
      convert labelled_nodup f hh using 2
      funext m
      dsimp [f]
      split <;> rfl
    · simp

theorem listed_path {ms : List Move} {cap : Nat} {layers : List (List WordState)} {s : WordState}
    (hm : ms ∈ listsOn cap layers s) : ms.length = layers.length ∧ Witness cap s source ms := by
  induction layers generalizing s ms with
  | nil =>
    rw [listsOn] at hm
    split at hm
    next h =>
      obtain ⟨hcap, he⟩ := h
      have hm0 : ms = [] := by simpa using hm
      subst ms
      exact ⟨rfl,he,hcap⟩
    next => simp at hm
  | cons layer layers ih =>
    rw [listsOn] at hm
    split at hm
    next hcap =>
      obtain ⟨m,_,hmem⟩ := List.mem_flatMap.mp hm
      simp only at hmem
      split at hmem
      · obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp hmem
        obtain ⟨hl,he,hp⟩ := ih ht
        exact ⟨congrArg Nat.succ hl,he,max_le hcap hp⟩
      · simp at hmem
    next => simp at hm

theorem at_least_106036_paths :
    ∃ paths : List (List Move), paths.Nodup ∧ paths.length = 106036 ∧
      ∀ ms ∈ paths, ms.length = 41 ∧ Witness 29 ak3 source ms := by
  refine ⟨listsOn 29 recordedLayers ak3, listsOn_nodup _ _ _,
    (listsOn_length _ _ _).trans recorded_counts.2, ?_⟩
  intro ms hm
  obtain ⟨hl,hw⟩ := listed_path hm
  exact ⟨hl.trans layer_count,hw⟩

private theorem cons_mem {cap : Nat} {m : Move} {ms : List Move} {s : WordState}
    {l : List WordState} {ls : List (List WordState)} :
    m :: ms ∈ listsOn cap (l::ls) s ↔ total s ≤ cap ∧ wordStep m s ∈ l ∧
    ms ∈ listsOn cap ls (wordStep m s) := by
  rw [listsOn]
  split
  next h =>
    simp only [h, true_and, List.mem_flatMap]
    constructor
    · rintro ⟨n,_,hh⟩
      change m :: ms ∈ (if wordStep n s ∈ l then (listsOn cap ls (wordStep n s)).map (n :: ·) else []) at hh
      split at hh
      next hx =>
        obtain ⟨ys,hy,he⟩ := List.mem_map.mp hh
        obtain ⟨rfl,rfl⟩ := List.cons.inj he
        exact ⟨hx,hy⟩
      next => simp at hh
    · rintro ⟨hv,hy⟩
      exact ⟨m,labels_complete _,by simpa [hv] using List.mem_map_of_mem (f := (m :: ·)) hy⟩
  next h => simp [h]

theorem monotone_membership {lo hi : Nat} (hle : lo ≤ hi) (ls : List (List WordState))
    (s : WordState) (ms : List Move) :
    ms ∈ listsOn lo ls s ↔ ms ∈ listsOn hi ls s ∧ peak ms s ≤ lo := by
  induction ls generalizing s ms with
  | nil =>
    by_cases he : s = source
    · subst s
      by_cases hlo : total source ≤ lo
      · have hhi := hlo.trans hle
        cases ms <;> simp [listsOn, hlo, hhi, peak]
      · by_cases hhi : total source ≤ hi <;> cases ms <;> simp [listsOn,hlo,hhi,peak]
    · simp [listsOn,he]
  | cons l ls ih =>
    cases ms with
    | nil =>
      have noNil (cap : Nat) : [] ∉ listsOn cap (l::ls) s := by
        intro h
        have hlen := (listed_path h).1
        simp at hlen
      simp [noNil]
    | cons m ms =>
      rw [cons_mem, cons_mem, ih, peak, max_le_iff]
      grind

/-- Genuine paths of peak exactly 29 within the deposited layers. -/
theorem at_least_34624_peak29 :
    ∃ paths : List (List Move), paths.Nodup ∧ paths.length = 34624 ∧
      ∀ ms ∈ paths, ms.length = 41 ∧ wordRun ms ak3 = source ∧ peak ms ak3 = 29 := by
  let allPaths := listsOn 29 recordedLayers ak3
  let low (ms : List Move) := decide (peak ms ak3 ≤ 28)
  have hal : allPaths.length = 106036 := (listsOn_length _ _ _).trans recorded_counts.2
  have hl : (allPaths.filter low).Perm (listsOn 28 recordedLayers ak3) := by
    apply (List.perm_ext_iff_of_nodup ((listsOn_nodup _ _ _).filter _ ) (listsOn_nodup _ _ _)).mpr
    intro ms
    simp only [List.mem_filter, low, decide_eq_true_eq]
    exact (monotone_membership (by decide : 28 ≤ 29) _ _ _).symm
  have hlow := hl.length_eq.trans ((listsOn_length _ _ _).trans recorded_counts.1)
  let high := allPaths.filter (fun ms => !low ms)
  refine ⟨high, (listsOn_nodup _ _ _).filter _, ?_, ?_⟩
  · have hsum := List.length_eq_length_filter_add (l := allPaths) low
    change high.length = 34624
    change allPaths.length = _ + high.length at hsum
    omega
  · intro ms hm
    obtain ⟨hall, hhi⟩ := List.mem_filter.mp hm
    obtain ⟨hlen, hrun, hpeak⟩ := listed_path hall
    have hgt : ¬peak ms ak3 ≤ 28 := by simpa [low] using hhi
    exact ⟨hlen.trans layer_count,hrun,by omega⟩

end Candidate.AK3Peak.FixedS
