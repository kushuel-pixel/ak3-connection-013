import Extension.FourWay
import Submission.EFamily

/-! Reachability equivalences do not assert the existence of a new bridge. -/
namespace Verify.Submission.Connections
open AtomicSemantics EntryExtension
open AK3Mod5FixedPointAdapter (originalStart)
open SevenPrefixUpperBound (groupRun_append)

def ak3 : GroupState := (x*y*x*Y*X*Y,x^3*Y^4)
def bridge42 : List Move :=
  [.m0,.m1,.m12,.m10,.m5,.m13,.m5,.m13,.m3,.m11,.m4,.m1,.m9,.m7,
   .m5,.m12,.m12,.m11,.m5,.m12,.m4,.m10,.m12,.m11,.m5,.m12,.m11,.m5,
   .m12,.m4,.m10,.m12,.m12,.m12,.m6,.m4,.m13,.m13,.m8,.m8,.m8,.m7]

theorem bridge42_length : bridge42.length = 42 := by decide +kernel
theorem bridge42_reaches : groupRun bridge42 ak3 = originalStart := by decide +kernel

def totalLength (s : GroupState) : Nat := s.1.toWord.length+s.2.toWord.length
def bridgeSizes : List Nat :=
  (List.range 43).map (fun k => totalLength (groupRun (bridge42.take k) ak3))

theorem bridge42_cap : ∀ k ∈ List.range 43,
    totalLength (groupRun (bridge42.take k) ak3) ≤ 22 := by decide +kernel
theorem bridge42_attains22 : 22 ∈ bridgeSizes := by decide +kernel

theorem ak3_to_S : Reach ak3 originalStart := ⟨bridge42,bridge42_reaches⟩
theorem S_to_ak3 : Reach originalStart ak3 := reach_symm ak3_to_S

theorem ak3_target_iff (t : GroupState) : Reach ak3 t ↔ Reach originalStart t := by
  constructor
  · exact fun h => reach_trans S_to_ak3 h
  · exact fun h => reach_trans ak3_to_S h

theorem S_standard_iff_hit :
    Reach originalStart (x,y) ↔ ∃ pre : List Move, FourWayHit (groupRun pre originalStart) := by
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨p,?_⟩
    rw [hp]
    exact Or.inl (Or.inl (by decide +kernel))
  · rintro ⟨pre,hit⟩
    obtain ⟨tail,h⟩ := four_way_to_standard (groupRun pre originalStart)
      (unit_run pre originalStart original_unit) hit
    exact ⟨pre++tail,by rw [groupRun_append,h]⟩

theorem member_standard (n : Nat) : Reach (ROperationConnection.initial n) (x,y) :=
  ⟨SevenPrefixUpperBound.word n,SevenPrefixUpperBound.reaches n⟩
theorem E_standard (n : Nat) : Reach (EFamily.initial n) (x,y) :=
  ⟨EFamily.word n,EFamily.reaches n⟩

theorem S_member_iff_standard (n : Nat) :
    Reach originalStart (ROperationConnection.initial n) ↔ Reach originalStart (x,y) := by
  constructor
  · exact fun h => reach_trans h (member_standard n)
  · exact fun h => reach_trans h (standard_to_member n)

theorem S_E_iff_standard (n : Nat) :
    Reach originalStart (EFamily.initial n) ↔ Reach originalStart (x,y) := by
  constructor
  · exact fun h => reach_trans h (E_standard n)
  · exact fun h => reach_trans h (reach_symm (E_standard n))

theorem ak3_E_iff_hit (n : Nat) :
    Reach ak3 (EFamily.initial n) ↔
      ∃ pre : List Move, FourWayHit (groupRun pre originalStart) := by
  rw [ak3_target_iff,S_E_iff_standard,S_standard_iff_hit]

theorem ak3_member_iff_hit (n : Nat) :
    Reach ak3 (ROperationConnection.initial n) ↔
      ∃ pre : List Move, FourWayHit (groupRun pre originalStart) := by
  rw [ak3_target_iff,S_member_iff_standard,S_standard_iff_hit]

end Verify.Submission.Connections
