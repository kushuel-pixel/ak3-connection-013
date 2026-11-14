import Extension.FourWay

namespace Verify.EntryExtension.Audit
open AtomicSemantics ROperationConnection
open AK3Mod5FixedPointAdapter (originalStart)
open AK3D3HRowConnection (D3)
open Independent.CountedHit (coreCount)

-- These three states all fail the previous second-relator x/X test.
def firstX : GroupState := rows D3
def secondY : GroupState := vars D3
def firstY : GroupState := rows (vars D3)

theorem fixture_first_x : UnitDet firstX ∧ FourWayHit firstX ∧ coreCount firstX.2 ≠ 1 := by
  decide +kernel
theorem fixture_second_y : UnitDet secondY ∧ FourWayHit secondY ∧ coreCount secondY.2 ≠ 1 := by
  decide +kernel
theorem fixture_first_y : UnitDet firstY ∧ FourWayHit firstY ∧ coreCount firstY.2 ≠ 1 := by
  decide +kernel

-- The new condition remains a sufficient test, not a complete primitive-word test.
def fibBasis : GroupState := groupRun [.m2,.m4,.m2,.m4] (x,y)
theorem fixture_not_complete : UnitDet fibBasis ∧ ¬ FourWayHit fibBasis := by decide +kernel
theorem fixture_basis_still_reaches : Reach fibBasis (x,y) := by
  apply reach_symm
  exact ⟨[.m2,.m4,.m2,.m4],rfl⟩

-- The unit determinant hypothesis is essential even for the new hit predicate.
theorem fixture_unit_required : FourWayHit (x*x,y) ∧ ¬ UnitDet (x*x,y) := by decide +kernel

example (s : GroupState) (u : UnitDet s) (h : FourWayHit s) (m : ℕ) :
    ∃ t : List AtomicSemantics.Move, groupRun t s = initial m :=
  four_way_to_member s u m h

example (pre : List AtomicSemantics.Move) (m : ℕ)
    (h : FourWayHit (groupRun pre originalStart)) :
    ∃ t : List AtomicSemantics.Move,
      groupRun (pre++t) originalStart = initial m ∧
      groupRun (AK3D3BranchConnection.inverseMoves (pre++t)) (initial m) = originalStart :=
  prefix_four_way_both_directions pre m h

example :
    (∃ p : List AtomicSemantics.Move, groupRun p originalStart = D3) ↔
      ∃ p : List AtomicSemantics.Move, FourWayHit (groupRun p originalStart) := d3_iff_four_way

example (m : ℕ) : Reach firstX (initial m) :=
  four_way_to_member firstX fixture_first_x.1 m fixture_first_x.2.1
example (m : ℕ) : Reach secondY (initial m) :=
  four_way_to_member secondY fixture_second_y.1 m fixture_second_y.2.1
example (m : ℕ) : Reach firstY (initial m) :=
  four_way_to_member firstY fixture_first_y.1 m fixture_first_y.2.1

end Verify.EntryExtension.Audit

#print axioms Verify.EntryExtension.count_to_member
#print axioms Verify.EntryExtension.four_way_to_member
#print axioms Verify.EntryExtension.prefix_four_way_both_directions
#print axioms Verify.EntryExtension.d3_iff_four_way
