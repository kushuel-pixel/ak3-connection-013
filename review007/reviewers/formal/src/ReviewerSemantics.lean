import Submission.Connections
import Submission.SixMixFinite
namespace Reviewer007Semantics
open Verify Verify.AtomicSemantics Verify.EntryExtension Verify.ResearchWords
open Verify.AK3Mod5FixedPointAdapter (originalStart)

-- All fourteen IDs and their ordered action, independently transcribed from paper §1.
example : ([Move.m0,.m1,.m2,.m3,.m4,.m5,.m6,.m7,.m8,.m9,.m10,.m11,.m12,.m13].map moveId) = List.range 14 := by decide +kernel
example (r s : F) :
  [groupStep .m0 (r,s),groupStep .m1 (r,s),groupStep .m2 (r,s),groupStep .m3 (r,s),
   groupStep .m4 (r,s),groupStep .m5 (r,s),groupStep .m6 (r,s),groupStep .m7 (r,s),
   groupStep .m8 (r,s),groupStep .m9 (r,s),groupStep .m10 (r,s),groupStep .m11 (r,s),
   groupStep .m12 (r,s),groupStep .m13 (r,s)] =
  [(r⁻¹,s),(r,s⁻¹),(r*s,s),(r*s⁻¹,s),(r,s*r),(r,s*r⁻¹),
   (x*r*X,s),(X*r*x,s),(y*r*Y,s),(Y*r*y,s),
   (r,x*s*X),(r,X*s*x),(r,y*s*Y),(r,Y*s*y)] := rfl
example (p q : List Move) (s : GroupState) : groupRun (p++q) s = groupRun q (groupRun p s) := Verify.SevenPrefixUpperBound.groupRun_append p q s

example (n : Nat) : Verify.Submission.EFamily.word n =
  [.m6] ++ List.replicate (n+1) .m9 ++ [.m5] ++ List.replicate (n+1) .m13 ++ [.m2] ++ List.replicate (n+1) .m12 ++ [.m3,.m4,.m2,.m5,.m2,.m8] := rfl
example (n : Nat) : Verify.SevenPrefixUpperBound.word n = [.m9,.m3,.m6,.m2,.m2,.m5,.m11] ++ List.replicate (n+1) .m2 := rfl
example : Verify.ROperationConnection.initial 0 = (Y,x) := Verify.SevenPrefixUpperBound.initial_zero
example : Verify.Submission.EFamily.initial 0 = (Y,x*x*Y*X*y) := Verify.Submission.EFamily.zero_initial
example : Verify.Submission.EFamily.initial 0 ≠ Verify.ROperationConnection.initial 0 := by decide +kernel
example : originalStart = (X*y^3*x*Y^4,x^2*Y^5*X*y^5) := rfl
example : originalStart ≠ Verify.Submission.EFamily.initial 3 := by decide +kernel
example : originalStart ≠ Verify.Submission.EFamily.initial 4 := by decide +kernel
example : (x,y) ≠ ((y,x) : GroupState) := by decide +kernel

-- coreCount counts both x orientations after cyclic reduction, rather than exponent sum.
example : Independent.CountedHit.coreCount (x*y*X*y) = 2 := by decide +kernel
example : Independent.CountedHit.coreCount (x*y*X) = 0 := by decide +kernel
example : FourWayHit ((1,x) : GroupState) := by decide +kernel
example : ¬ UnitDet ((1,x) : GroupState) := by decide +kernel
example : ¬ Reach ((1,x) : GroupState) (x,y) := by
  intro h
  obtain ⟨ms,hm⟩ := reach_symm h
  have hu : UnitDet (groupRun ms (x,y)) := unit_run ms (x,y) (Or.inl (by decide +kernel))
  rw [hm] at hu
  exact (by decide +kernel : ¬ UnitDet ((1,x) : GroupState)) hu

-- Asymmetric matrix fixture detects left/right reversal, beyond invariant census counts.
example : Verify.Submission.SixMixFinite.name 1 = "FQQQQQ" := by decide +kernel
example : Verify.Submission.SixMixFinite.product 1 63 = ⟨1,1,5,6⟩ := by decide +kernel
example : Verify.Submission.SixMixFinite.product 1 63 ≠ ⟨6,1,5,1⟩ := by decide +kernel
end Reviewer007Semantics
