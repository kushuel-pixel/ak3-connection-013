import CompactSound
import StreamCut

namespace Candidate.AK3Peak.FixedS.LayerChecks
open Verify.AtomicSemantics
open AK3Compact (Key encode children)
abbrev RowsByDepth := Nat → List Key

def members (rows : RowsByDepth) : StreamCut.Layers := fun i s => encode s ∈ rows i

def checks (rows : RowsByDepth) (cap r : Nat) : Bool :=
  (List.range r).all fun i =>
    let targets := (List.range (i+2)).flatMap rows
    (rows i).all fun k => (children none cap k).all (fun j => targets.contains j)

theorem cover_of_checks {cap r : Nat} {s : WordState} {rows : RowsByDepth}
    (root : encode s ∈ rows 0) (hc : checks rows cap r = true) :
    StreamCut.Cover cap r s (members rows) := by
  refine ⟨root,?_⟩
  intro i hi u hu m ht
  have hj : encode (wordStep m u) ∈ children none cap (encode u) := by
    apply List.mem_filterMap.mpr
    refine ⟨moveId m,BallSearch.mem_moveIds m,?_⟩
    simp only [CompactSound.decode_encode, BallSearch.step_eq]
    change (if total (wordStep m u) ≤ cap then _ else _) = _
    rw [ite_eq_left ht]
    rfl
  have h1 := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 (encode u) hu
  have h3 := List.all_eq_true.mp h2 _ hj
  have hmem : encode (wordStep m u) ∈ (List.range (i+2)).flatMap rows := by
    simpa using h3
  obtain ⟨j,hj',he⟩ := List.mem_flatMap.mp hmem
  exact ⟨j,by have := List.mem_range.mp hj'; omega,he⟩

end Candidate.AK3Peak.FixedS.LayerChecks
