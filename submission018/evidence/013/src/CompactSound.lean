import CompactEngine
import B5BallSearch
import FixedSCuts

namespace Candidate.AK3Peak.FixedS.CompactSound
open Verify.AtomicSemantics
open AK3Compact (Key Ban Table Layer prepend encode decode permitted children add visit advance ball separate)

private theorem prepend_ge (w : Word) (n : Nat) (hn : 1 ≤ n) : 1 ≤ prepend w n := by
  induction w with
  | nil => exact hn
  | cons a w ih => simp only [prepend]; omega

private theorem decode_prepend (u v : Word) :
    decode (prepend u (5 * AK3BallEngine.pack v + 4)) = (u,v) := by
  induction u with
  | nil =>
    have hp := BallSearch.one_le_pack v
    change decode (5 * AK3BallEngine.pack v + 4) = ([], v)
    rw [decode, ite_eq_right (by omega)]
    rw [ite_eq_left (by omega), show (5 * AK3BallEngine.pack v + 4) / 5 = AK3BallEngine.pack v by omega,
      BallSearch.unpack_pack]
  | cons a u ih =>
    let n := prepend u (5 * AK3BallEngine.pack v + 4)
    have hp : 1 ≤ n := prepend_ge _ _ (by omega)
    have hd := BallSearch.digit_lt a
    change decode (5*n + AK3BallEngine.digit a) = (a::u,v)
    rw [decode, ite_eq_right (by omega), ite_eq_right (by omega),
      show (5*n + AK3BallEngine.digit a) / 5 = n by omega,
      show (5*n + AK3BallEngine.digit a) % 5 = AK3BallEngine.digit a by omega,
      show decode n = (u,v) from ih, BallSearch.letter_digit]

@[simp] theorem decode_encode (s : WordState) : decode (encode s) = s := decode_prepend _ _

theorem encode_injective : Function.Injective encode := by
  intro a b h
  simpa only [decode_encode] using congrArg decode h

private theorem add_fold (ks : List Key) (b : Layer) (j : Key) :
    (j ∈ (ks.foldl add b).seen ↔ j ∈ b.seen ∨ j ∈ ks) ∧
    (j ∈ (ks.foldl add b).front ↔ j ∈ b.front ∨ (j ∉ b.seen ∧ j ∈ ks)) := by
  induction ks generalizing b with
  | nil => simp
  | cons k ks ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [(ih (add b k)).1, (ih (add b k)).2]
    by_cases hk : k ∈ b.seen
    · simp only [add, ite_eq_left hk]
      grind
    · simp only [add, ite_eq_right hk, Std.HashSet.mem_insert, List.mem_cons]
      grind

private theorem visit_fold (ban : Ban) (cap : Nat) (ks : List Key) (b : Layer) (j : Key) :
    (j ∈ (ks.foldl (visit ban cap) b).seen ↔ j ∈ b.seen ∨ ∃ k ∈ ks, j ∈ children ban cap k) ∧
    (j ∈ (ks.foldl (visit ban cap) b).front ↔ j ∈ b.front ∨
      (j ∉ b.seen ∧ ∃ k ∈ ks, j ∈ children ban cap k)) := by
  induction ks generalizing b with
  | nil => simp
  | cons k ks ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [(ih (visit ban cap b k)).1, (ih (visit ban cap b k)).2]
    simp only [visit, (add_fold (children ban cap k) b j).1,
      (add_fold (children ban cap k) b j).2]
    grind

private theorem old_seen {ban : Ban} {cap : Nat} {b : Layer} {j : Key} (h : j ∈ b.seen) :
    j ∈ (advance ban cap b).seen :=
  (visit_fold ban cap b.front ⟨b.seen,[]⟩ j).1.mpr (Or.inl h)

private theorem next_seen {ban : Ban} {cap : Nat} {b : Layer} {k j : Key}
    (hk : k ∈ b.front) (hj : j ∈ children ban cap k) : j ∈ (advance ban cap b).seen :=
  (visit_fold ban cap b.front ⟨b.seen,[]⟩ j).1.mpr (Or.inr ⟨k,hk,hj⟩)

private theorem closed (ban : Ban) (cap r : Nat) (s : WordState) :
    ∀ k ∈ (ball ban cap s r).seen, k ∉ (ball ban cap s r).front →
    ∀ j ∈ children ban cap k, j ∈ (ball ban cap s r).seen := by
  induction r with
  | zero =>
    intro k hk hn
    simp only [ball, Std.HashSet.mem_insert, Std.HashSet.not_mem_empty, or_false] at hk
    exact False.elim (hn (by simp only [ball, List.mem_singleton]; exact (beq_iff_eq.mp hk).symm))
  | succ r ih =>
    let b := ball ban cap s r
    intro k hk hn j hj
    have hs := (visit_fold ban cap b.front ⟨b.seen,[]⟩ k).1.mp hk
    have hprev : k ∈ b.seen := by
      rcases hs with hs | hs
      · exact hs
      · by_contra habs
        exact hn ((visit_fold ban cap b.front ⟨b.seen,[]⟩ k).2.mpr (Or.inr ⟨habs,hs⟩))
    by_cases hf : k ∈ b.front
    · exact next_seen hf hj
    · exact old_seen (ih k hprev hf j hj)

def permits (ban : Ban) : List Move → WordState → Bool
  | [], _ => true
  | m::ms, s => permitted ban (encode s) (encode (wordStep m s)) && permits ban ms (wordStep m s)

private theorem permits_append (ban : Ban) (xs ys : List Move) (s : WordState) :
    permits ban (xs++ys) s = (permits ban xs s && permits ban ys (wordRun xs s)) := by
  induction xs generalizing s with
  | nil => rfl
  | cons m xs ih => simp only [List.cons_append, permits, wordRun, ih, Bool.and_assoc]

private theorem step_seen {ban : Ban} {cap n : Nat} {s u : WordState} (m : Move)
    (hu : encode u ∈ (ball ban cap s n).seen) (ht : total (wordStep m u) ≤ cap)
    (hok : permitted ban (encode u) (encode (wordStep m u)) = true) :
    encode (wordStep m u) ∈ (ball ban cap s (n+1)).seen := by
  have child : encode (wordStep m u) ∈ children ban cap (encode u) := by
    apply List.mem_filterMap.mpr
    refine ⟨moveId m, BallSearch.mem_moveIds m, ?_⟩
    simp only [decode_encode, BallSearch.step_eq]
    change (if total (wordStep m u) ≤ cap then
      (if permitted ban (encode u) (encode (wordStep m u)) then some (encode (wordStep m u)) else none)
      else none) = _
    simp [ht, hok]
  by_cases hf : encode u ∈ (ball ban cap s n).front
  · exact next_seen hf child
  · exact old_seen (closed ban cap n s _ hu hf _ child)

theorem cover {ban : Ban} {cap n : Nat} {s : WordState} {ms : List Move}
    (hm : ms.length ≤ n) (hp : peak ms s ≤ cap) (ha : permits ban ms s = true) :
    encode (wordRun ms s) ∈ (ball ban cap s n).seen := by
  induction n generalizing ms with
  | zero =>
    have hz : ms = [] := List.length_eq_zero_iff.mp (by omega)
    subst ms
    exact Std.HashSet.mem_insert_self
  | succ n ih =>
    cases hl : ms.getLast? with
    | none =>
      have hz : ms = [] := List.getLast?_eq_none_iff.mp hl
      subst ms
      exact old_seen (ih (ms := []) (by simp) hp ha)
    | some m =>
      obtain ⟨xs,rfl⟩ := List.getLast?_eq_some_iff.mp hl
      have hxs : xs.length ≤ n := by simpa using hm
      rw [peak_append] at hp
      rw [permits_append, Bool.and_eq_true] at ha
      rw [run_append]
      apply step_seen m (ih hxs (max_le_iff.mp hp).1 ha.1)
      · exact (end_le_peak [m] _).trans (max_le_iff.mp hp).2
      · simpa only [permits, Bool.and_true] using ha.2

theorem checked_cut {ban : Ban} {cap r t : Nat} (hc : separate ban cap r t ak3 source = true)
    {u : WordState} {xs ys : List Move} (hx : xs.length ≤ r) (hy : ys.length ≤ t)
    (wx : Witness cap ak3 u xs) (wy : Witness cap source u ys)
    (ax : permits ban xs ak3 = true) (ay : permits ban ys source = true) : False := by
  have ha := cover hx wx.2 ax
  have hb := cover hy wy.2 ay
  rw [wx.1] at ha
  rw [wy.1] at hb
  have hh := Std.HashSet.all_eq_true_iff_forall_mem.mp hc (encode u) ha
  simp [show (ball ban cap source t).seen.contains (encode u) = true from hb] at hh

theorem unrestricted (ms : List Move) (s : WordState) : permits none ms s = true := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => exact ih _

theorem bans_edge (ms : List Move) (s : WordState) :
    permits (some (encode U,encode V)) ms s = avoids ms s := by
  have eqtest (u v : WordState) : (encode u == encode v) = (u == v) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, encode_injective.eq_iff]
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => simp only [permits, avoids, permitted, allowed, eqtest, ih]

theorem ordinary_of_check {cap r t : Nat} (hc : separate none cap r t ak3 source = true) :
    OrdinaryCut cap r t := by
  intro u ⟨xs,hx,wx⟩ ⟨ys,hy,wy⟩
  exact checked_cut hc hx hy wx wy (unrestricted _ _) (unrestricted _ _)

theorem deleted_of_check {cap r t : Nat}
    (hc : separate (some (encode U,encode V)) cap r t ak3 source = true) : DeletedCut cap r t := by
  intro u ⟨xs,hx,wx,ax⟩ ⟨ys,hy,wy,ay⟩
  exact checked_cut hc hx hy wx wy ((bans_edge _ _).trans ax) ((bans_edge _ _).trans ay)

end Candidate.AK3Peak.FixedS.CompactSound
