import Adjacent.Distance

/-! Classify both length-three halves in the original canonical words.
The midpoint tag is only a certificate: its behavior on every triple of IDs
is checked inside Lean. -/
namespace Verify.AdjacentGeodesics

open AtomicSemantics
open ROperationConnection (initial)
open SevenPrefixUpperBound (canonicalInitial canonicalInitial_reduced eval_canonicalInitial groupRun_append)
open AK3D3BranchConnection (inverseMove inverseMoves groupRun_inverse)

private def ids : List Move :=
  [.m0,.m1,.m2,.m3,.m4,.m5,.m6,.m7,.m8,.m9,.m10,.m11,.m12,.m13]

private theorem exhaustive (a : Move) : a ∈ ids := by cases a <;> decide

private def tripleTest (p : Move → Move → Move → Bool) : Bool :=
  ids.all fun a => ids.all fun b => ids.all fun c => p a b c

private theorem tripleTest_sound (p : Move → Move → Move → Bool) (h : tripleTest p = true)
    (a b c : Move) : p a b c = true :=
  List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h a (exhaustive a)) b
    (exhaustive b)) c (exhaustive c)

private def letterAt (w : Word) (k : ℕ) : ℕ :=
  match w[k]? with
  | none => 0
  | some (g,sgn) => if g.val = 0 then (if sgn then 1 else 2) else (if sgn then 3 else 4)

private def tag (s : WordState) : ℕ :=
  match s.2.length with
  | 3 => match s.1.length with
    | 8 => 2
    | _ => 0
  | 4 => match letterAt s.2 3 with
    | 1 => match letterAt s.1 9 with
      | 4 => match letterAt s.1 11 with
        | 0 => match letterAt s.1 0 with
          | 3 => match letterAt s.1 3 with
            | 3 => 2
            | _ => 0
          | 4 => 2
          | _ => 0
        | 2 => match letterAt s.1 0 with
          | 3 => 0
          | _ => 2
        | 4 => match letterAt s.1 6 with
          | 1 => match letterAt s.1 1 with
            | 3 => 0
            | _ => 2
          | 4 => match letterAt s.1 0 with
            | 2 => match letterAt s.1 1 with
              | 3 => match s.1.length with
                | 17 => 0
                | _ => 2
              | _ => 0
            | _ => 0
          | _ => 0
        | _ => 0
      | _ => 0
    | 3 => match s.1.length with
      | 11 => match letterAt s.1 1 with
        | 3 => 2
        | _ => 0
      | _ => 0
    | 4 => match s.1.length with
      | 11 => match letterAt s.1 5 with
        | 1 => match letterAt s.1 1 with
          | 3 => 2
          | _ => 0
        | _ => 0
      | _ => 0
    | _ => 0
  | 5 => match s.1.length with
    | 4 => 1
    | 7 => 0
    | 9 => 0
    | 11 => match letterAt s.1 1 with
      | 2 => match letterAt s.1 5 with
        | 3 => 2
        | _ => 0
      | 4 => match letterAt s.1 0 with
        | 4 => 2
        | _ => 0
      | _ => 2
    | 14 => match letterAt s.1 0 with
      | 2 => match letterAt s.2 0 with
        | 4 => 2
        | _ => 0
      | 4 => 0
      | _ => 2
    | _ => 2
  | 6 => match letterAt s.2 1 with
    | 1 => match letterAt s.2 0 with
      | 4 => 2
      | _ => 0
    | 2 => match s.1.length with
      | 11 => 2
      | _ => 0
    | 3 => match letterAt s.2 4 with
      | 3 => match s.1.length with
        | 11 => 2
        | _ => 0
      | _ => 0
    | 4 => match letterAt s.1 5 with
      | 1 => match letterAt s.1 1 with
        | 3 => 2
        | _ => 0
      | 4 => match s.1.length with
        | 11 => 2
        | _ => 0
      | _ => 2
    | _ => 0
  | 7 => match letterAt s.2 2 with
    | 1 => match s.1.length with
      | 9 => 0
      | _ => 2
    | 3 => match letterAt s.2 5 with
      | 2 => match s.1.length with
        | 9 => 0
        | _ => 2
      | 3 => 2
      | _ => 0
    | 4 => match s.1.length with
      | 4 => match letterAt s.2 0 with
        | 3 => 2
        | _ => 0
      | 9 => 0
      | 11 => match letterAt s.2 1 with
        | 1 => match letterAt s.1 4 with
          | 1 => 0
          | _ => 2
        | 4 => 2
        | _ => 0
      | 14 => match letterAt s.1 8 with
        | 4 => 2
        | _ => 0
      | 16 => match letterAt s.2 1 with
        | 2 => 0
        | _ => 2
      | _ => 2
    | _ => 0
  | 8 => match letterAt s.2 2 with
    | 1 => match letterAt s.2 3 with
      | 4 => 0
      | _ => 2
    | 3 => match s.1.length with
      | 9 => 0
      | _ => 2
    | 4 => match s.1.length with
      | 9 => 0
      | _ => 2
    | _ => 2
  | 9 => match letterAt s.2 2 with
    | 1 => match s.1.length with
      | 9 => 0
      | 11 => match letterAt s.1 9 with
        | 4 => 2
        | _ => 0
      | _ => 2
    | 3 => match letterAt s.2 5 with
      | 3 => 2
      | _ => 0
    | 4 => match s.1.length with
      | 11 => match letterAt s.1 0 with
        | 3 => 0
        | _ => 2
      | _ => 0
    | _ => 0
  | 10 => match letterAt s.1 10 with
    | 0 => 0
    | 1 => match letterAt s.2 0 with
      | 1 => 0
      | _ => 2
    | _ => 2
  | 11 => match s.1.length with
    | 4 => match letterAt s.1 0 with
      | 3 => 0
      | _ => 2
    | 7 => 0
    | 9 => 0
    | 11 => match letterAt s.1 0 with
      | 3 => 0
      | _ => 2
    | 13 => match letterAt s.1 1 with
      | 3 => 0
      | _ => 2
    | 15 => 0
    | 16 => match letterAt s.1 9 with
      | 3 => 2
      | 4 => 2
      | _ => 0
    | 18 => match letterAt s.2 0 with
      | 3 => 2
      | _ => 0
    | _ => 2
  | 12 => match s.1.length with
    | 9 => 0
    | _ => 2
  | 13 => match s.1.length with
    | 5 => 2
    | 8 => 2
    | 10 => 2
    | 16 => match letterAt s.2 6 with
      | 3 => 0
      | _ => 2
    | 18 => 2
    | 19 => 2
    | 21 => 2
    | _ => 0
  | 14 => match s.1.length with
    | 11 => 2
    | _ => 0
  | 15 => match s.1.length with
    | 8 => 2
    | 10 => 2
    | 11 => match letterAt s.2 3 with
      | 1 => match letterAt s.1 0 with
        | 3 => 0
        | _ => 2
      | _ => 0
    | 16 => match letterAt s.2 3 with
      | 4 => 0
      | _ => 2
    | 18 => 2
    | _ => 0
  | 16 => match s.1.length with
    | 9 => 0
    | 11 => match letterAt s.2 2 with
      | 2 => 0
      | 4 => match letterAt s.2 8 with
        | 1 => match letterAt s.1 0 with
          | 3 => 0
          | _ => 2
        | _ => 2
      | _ => 2
    | 25 => match letterAt s.1 0 with
      | 3 => 2
      | _ => 0
    | _ => 2
  | 17 => match s.1.length with
    | 11 => match letterAt s.2 1 with
      | 1 => 0
      | _ => 2
    | _ => 0
  | 18 => match s.1.length with
    | 7 => match letterAt s.1 0 with
      | 2 => 0
      | _ => 2
    | 9 => 0
    | 11 => match letterAt s.2 2 with
      | 2 => 0
      | 3 => match letterAt s.1 0 with
        | 3 => 0
        | _ => 2
      | _ => 2
    | _ => 2
  | 19 => match s.1.length with
    | 13 => match letterAt s.1 1 with
      | 3 => 0
      | _ => 2
    | 15 => 0
    | _ => 2
  | 21 => match s.1.length with
    | 15 => 0
    | 17 => 0
    | _ => 2
  | 22 => 0
  | 23 => match letterAt s.2 1 with
    | 3 => 0
    | _ => 2
  | 24 => 0
  | 25 => match s.1.length with
    | 18 => 2
    | _ => 0
  | 30 => match s.1.length with
    | 13 => 0
    | _ => 2
  | 31 => 0
  | 35 => 0
  | _ => 2

private def leftTag (a b c : Move) : ℕ :=
  if [a,b,c] = [.m11,.m4,.m3] then 1 else 0

private def rightTag (d e f : Move) : ℕ :=
  if [d,e,f] = [.m9,.m2,.m8] ∨ [d,e,f] = [.m12,.m2,.m13] then 1 else 2

private def frontCheck (a b c : Move) : Bool :=
  decide (tag (wordRun [a,b,c] (canonicalInitial 3)) = leftTag a b c)
private def backCheck (d e f : Move) : Bool :=
  decide (tag (wordRun [inverseMove f,inverseMove e,inverseMove d] (canonicalInitial 4)) = rightTag d e f)

private theorem front_ok : tripleTest frontCheck = true := by decide +kernel
private theorem back_ok : tripleTest backCheck = true := by decide +kernel

private theorem only_six (a b c d e f : Move)
    (ends : groupRun [a,b,c,d,e,f] (initial 3) = initial 4) :
    [a,b,c,d,e,f] = [.m11,.m4,.m3,.m9,.m2,.m8] ∨
    [a,b,c,d,e,f] = [.m11,.m4,.m3,.m12,.m2,.m13] := by
  have back := groupRun_inverse [d,e,f] (groupRun [a,b,c] (initial 3))
  change groupRun [inverseMove f,inverseMove e,inverseMove d]
    (groupRun [a,b,c,d,e,f] (initial 3)) = groupRun [a,b,c] (initial 3) at back
  rw [ends] at back
  have middle : wordRun [inverseMove f,inverseMove e,inverseMove d] (canonicalInitial 4) =
      wordRun [a,b,c] (canonicalInitial 3) := by
    rw [wordRun_canonical _ _ (canonicalInitial_reduced 4),
      wordRun_canonical _ _ (canonicalInitial_reduced 3),eval_canonicalInitial,eval_canonicalInitial,back]
  have lhs : tag (wordRun [a,b,c] (canonicalInitial 3)) = leftTag a b c :=
    of_decide_eq_true (tripleTest_sound _ front_ok a b c)
  have rhs : tag (wordRun [inverseMove f,inverseMove e,inverseMove d] (canonicalInitial 4)) =
      rightTag d e f := of_decide_eq_true (tripleTest_sound _ back_ok d e f)
  rw [middle,lhs] at rhs
  by_cases front : [a,b,c] = [.m11,.m4,.m3]
  · have tail : [d,e,f] = [.m9,.m2,.m8] ∨ [d,e,f] = [.m12,.m2,.m13] := by
      by_contra no
      have absurdEq : (1 : ℕ) = 2 := by
        simpa only [leftTag, rightTag, ite_eq_left front, ite_eq_right no] using rhs
      exact (by decide : (1 : ℕ) ≠ 2) absurdEq
    change [a,b,c] ++ [d,e,f] = _ ∨ [a,b,c] ++ [d,e,f] = _
    rw [front]
    rcases tail with h|h
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; rfl)
  · simp only [leftTag,front,↓reduceIte,rightTag] at rhs
    split at rhs <;> contradiction

/-- Exact lists in the full 14-move model; inverse words and component swaps
are not identified. The separate distance theorem rules out every shorter list. -/
theorem d3_six_iff (ms : List Move) :
    (ms.length = 6 ∧ groupRun ms (initial 3) = initial 4) ↔
      ms = [.m11,.m4,.m3,.m9,.m2,.m8] ∨ ms = [.m11,.m4,.m3,.m12,.m2,.m13] := by
  constructor
  · rintro ⟨len,ends⟩
    match ms with
    | [a,b,c,d,e,f] => exact only_six a b c d e f ends
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] => simp at len
    | _::_::_::_::_::_::_::_ => simp at len
  · rintro (rfl|rfl)
    · exact ⟨rfl,AdjacentFamily.adjacent_via_first 3⟩
    · exact ⟨rfl,AdjacentFamily.adjacent_via_second 3⟩

/-- For six-step routes this characterizes exactly which literal lists meet a cap. -/
theorem d3_six_cap_iff (ms : List Move) (cap : ℕ) :
    ((ms.length = 6 ∧ groupRun ms (initial 3) = initial 4) ∧
      (AdjacentFamily.lengthTrace ms (canonicalInitial 3)).foldl max 0 ≤ cap) ↔
    (ms = [.m11,.m4,.m3,.m9,.m2,.m8] ∧ 16 ≤ cap) ∨
    (ms = [.m11,.m4,.m3,.m12,.m2,.m13] ∧ 18 ≤ cap) := by
  rw [d3_six_iff]
  constructor
  · rintro ⟨(rfl|rfl), hc⟩
    · rw [AdjacentFamily.d3_first_trace] at hc
      exact Or.inl ⟨rfl,hc⟩
    · rw [AdjacentFamily.d3_second_trace] at hc
      exact Or.inr ⟨rfl,hc⟩
  · rintro (⟨rfl,hc⟩|⟨rfl,hc⟩)
    · exact ⟨Or.inl rfl, by rw [AdjacentFamily.d3_first_trace]; exact hc⟩
    · exact ⟨Or.inr rfl, by rw [AdjacentFamily.d3_second_trace]; exact hc⟩

end Verify.AdjacentGeodesics
