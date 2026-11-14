import Extension.FourWay

namespace IndependentReview
open Verify Verify.AtomicSemantics Verify.EntryExtension
open Verify.AK3Mod5FixedPointAdapter (originalStart)
open Verify.ROperationConnection (initial)
open Independent.CountedHit (coreCount)

-- This consumer states all four branches directly, without assuming FourWayHit.
theorem arbitrary_pair_entry :
    ∀ (a b : F) (m : ℕ),
      (OneRelatorEntry.det (a,b) = 1 ∨ OneRelatorEntry.det (a,b) = -1) →
      (coreCount a = 1 ∨ coreCount (rename a) = 1 ∨
        coreCount b = 1 ∨ coreCount (rename b) = 1) →
      ∃ ms : List Move, groupRun ms (a,b) = initial m := by
  intro a b m determinant hit
  apply four_way_to_member (a,b) determinant m
  rcases hit with h|h|h|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem exact_prefix_and_reverse (pre : List Move) (m : ℕ)
    (h : FourWayHit (groupRun pre originalStart)) :
    ∃ tail : List Move,
      groupRun (pre++tail) originalStart = initial m ∧
      groupRun (Verify.AK3D3BranchConnection.inverseMoves (pre++tail)) (initial m) = originalStart := by
  exact prefix_four_way_both_directions pre m h

example (s : GroupState) (m : Move) :
    groupStep (rowMove m) (rows s) = rows (groupStep m s) := rows_step m s
example (s : GroupState) (m : Move) :
    groupStep (varMove m) (vars s) = vars (groupStep m s) := vars_step m s

end IndependentReview
#check IndependentReview.arbitrary_pair_entry
#print axioms IndependentReview.arbitrary_pair_entry
#check IndependentReview.exact_prefix_and_reverse
#print axioms IndependentReview.exact_prefix_and_reverse
