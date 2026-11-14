import Extension.Symmetries

/-! An entry may occur in either relator, with either generator singled out.
All continuations use the original fourteen atomic moves. -/
namespace Verify.EntryExtension
open AtomicSemantics
open ROperationConnection (initial)
open Independent.CountedHit (coreCount)
open SevenPrefixUpperBound (groupRun_append)
open AK3Mod5FixedPointAdapter (originalStart)
open AK3D3HRowConnection (D3)

def AxisHit (g : F) : Prop := coreCount g = 1 ∨ coreCount (rename g) = 1
def FourWayHit (s : GroupState) : Prop := AxisHit s.1 ∨ AxisHit s.2

instance axisHitDecidable (g : F) : Decidable (AxisHit g) := by
  unfold AxisHit
  infer_instance
instance fourWayHitDecidable (s : GroupState) : Decidable (FourWayHit s) := by
  unfold FourWayHit
  infer_instance

theorem axis_second_to_standard (s : GroupState) (unit : UnitDet s)
    (hit : AxisHit s.2) : Reach s (x,y) := by
  rcases hit with hx|hy
  · exact count_to_standard s unit hx
  · apply vars_to_standard s
    exact count_to_standard (vars s) (unit_vars s unit) hy

theorem four_way_to_standard (s : GroupState) (unit : UnitDet s)
    (hit : FourWayHit s) : Reach s (x,y) := by
  rcases hit with first|second
  · apply rows_to_standard s
    exact axis_second_to_standard (rows s) (unit_rows s unit) first
  · exact axis_second_to_standard s unit second

theorem four_way_to_member (s : GroupState) (unit : UnitDet s) (m : ℕ)
    (hit : FourWayHit s) : Reach s (initial m) := by
  exact reach_trans (four_way_to_standard s unit hit) (standard_to_member m)

/-- The originally discovered prefix is retained, not replaced by a new route. -/
theorem prefix_four_way_to_member (pre : List Move) (m : ℕ)
    (hit : FourWayHit (groupRun pre originalStart)) :
    ∃ tail : List Move, groupRun (pre++tail) originalStart = initial m := by
  obtain ⟨tail,ht⟩ := four_way_to_member (groupRun pre originalStart)
    (unit_run pre originalStart original_unit) m hit
  exact ⟨tail,by rw [groupRun_append,ht]⟩

/-- This also supplies the reverse route from every family member to S. -/
theorem prefix_four_way_both_directions (pre : List Move) (m : ℕ)
    (hit : FourWayHit (groupRun pre originalStart)) :
    ∃ tail : List Move,
      groupRun (pre++tail) originalStart = initial m ∧
      groupRun (AK3D3BranchConnection.inverseMoves (pre++tail)) (initial m) = originalStart := by
  obtain ⟨tail,h⟩ := prefix_four_way_to_member pre m hit
  refine ⟨tail,h,?_⟩
  rw [← h]
  exact AK3D3BranchConnection.groupRun_inverse (pre++tail) originalStart

/-- Unbounded reachability only: no claim about first-hit depth or a peak cap. -/
theorem d3_iff_four_way :
    (∃ p : List Move, groupRun p originalStart = D3) ↔
    ∃ p : List Move, FourWayHit (groupRun p originalStart) := by
  constructor
  · rintro ⟨p,h⟩
    refine ⟨p,?_⟩
    rw [h]
    exact Or.inr (Or.inl (by decide +kernel))
  · rintro ⟨p,h⟩
    obtain ⟨tail,e⟩ := prefix_four_way_to_member p 3 h
    exact ⟨p++tail,e⟩

end Verify.EntryExtension
