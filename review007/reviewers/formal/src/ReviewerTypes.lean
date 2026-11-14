import Submission.Connections
import Submission.SixMixFinite

namespace Reviewer007
open Verify Verify.AtomicSemantics Verify.EntryExtension Verify.ResearchWords
open Verify.AK3Mod5FixedPointAdapter (originalStart)

namespace E
open Verify.Submission.EFamily
example : ∀ (k : Nat) (r s : F), groupRun (List.replicate k .m9) (r,s) = (Y^k*r*y^k,s) := run_first_Y
example : ∀ (k : Nat) (r s : F), groupRun (List.replicate k .m13) (r,s) = (r,Y^k*s*y^k) := run_second_Y
example : ∀ (k : Nat) (r s : F), groupRun (List.replicate k .m12) (r,s) = (r,y^k*s*Y^k) := run_second_y
example : ∀ n : Nat, groupRun (prefixMoves n) (initial n) = (central n,second n) := prefix_run
example : ∀ n : Nat, groupStep .m5 (central n,second n) = (central n,x*y) := first_mix
example : ∀ n : Nat, groupRun (List.replicate (n+1) .m13) (central n,x*y) = (central n,Y^(n+1)*x*y^((n+1)+1)) := second_conjugations
example : ∀ n : Nat, groupStep .m2 (central n,Y^(n+1)*x*y^((n+1)+1)) = (Y*x*y,Y^(n+1)*x*y^((n+1)+1)) := second_mix
example : ∀ n : Nat, groupRun (List.replicate (n+1) .m12) (Y*x*y,Y^(n+1)*x*y^((n+1)+1)) = (Y*x*y,x*y) := restore_second
example : groupRun suffix (Y*x*y,x*y) = (x,y) := suffix_run
example : ∀ n : Nat, groupRun (word n) (initial n) = (x,y) := reaches
example : ∀ n : Nat, (word n).length = 3*n+12 := word_length
example : ∀ n : Nat, wordRun (word n) (canonicalInitial n) = ([Verify.ReducedWords.xLetter],[Verify.ReducedWords.yLetter]) := canonical_reaches
example : initial 0 = (Y,x*x*Y*X*y) := zero_initial
end E

namespace C
open Verify.Submission.Connections
example : bridge42.length = 42 := bridge42_length
example : groupRun bridge42 ak3 = originalStart := bridge42_reaches
example : ∀ k ∈ List.range 43, totalLength (groupRun (bridge42.take k) ak3) ≤ 22 := bridge42_cap
example : 22 ∈ bridgeSizes := bridge42_attains22
example : Reach ak3 originalStart := ak3_to_S
example : Reach originalStart ak3 := S_to_ak3
example : ∀ t : GroupState, Reach ak3 t ↔ Reach originalStart t := ak3_target_iff
example : Reach originalStart (x,y) ↔ ∃ pre : List Move, FourWayHit (groupRun pre originalStart) := S_standard_iff_hit
example : ∀ n : Nat, Reach (Verify.ROperationConnection.initial n) (x,y) := member_standard
example : ∀ n : Nat, Reach (Verify.Submission.EFamily.initial n) (x,y) := E_standard
example : ∀ n : Nat, Reach originalStart (Verify.ROperationConnection.initial n) ↔ Reach originalStart (x,y) := S_member_iff_standard
example : ∀ n : Nat, Reach originalStart (Verify.Submission.EFamily.initial n) ↔ Reach originalStart (x,y) := S_E_iff_standard
example : ∀ n : Nat, Reach ak3 (Verify.Submission.EFamily.initial n) ↔ ∃ pre : List Move, FourWayHit (groupRun pre originalStart) := ak3_E_iff_hit
example : ∀ n : Nat, Reach ak3 (Verify.ROperationConnection.initial n) ↔ ∃ pre : List Move, FourWayHit (groupRun pre originalStart) := ak3_member_iff_hit
end C

namespace S
open Verify.Submission.SixMixFinite
example : count unit = 244 := identity_profiles
example : count negUnit = 16 := negative_identity_profiles
example : viable.length = 22 := viable_layouts
example : residual.length = 16 := residual_layouts
example : residualCount unit = 156 := residual_identity_profiles
example : residualCount negUnit = 16 := residual_negative_profiles
example : residual.map name = ["QFFQQQ", "FQQFQQ", "QQFFQQ", "QFQQFQ", "FQFQFQ", "QQQFFQ", "FFQFFQ", "QFFFFQ", "FQQQQF", "QQFQQF", "FFFQQF", "QFQFQF", "FQFFQF", "FFQQFF", "QFFQFF", "FQQFFF"] := residual_names
end S

-- Inherited contracts: hypotheses remain explicit and prefixes are retained.
example : ∀ (s : GroupState), UnitDet s → FourWayHit s → Reach s (x,y) := four_way_to_standard
example : ∀ (s : GroupState), UnitDet s → ∀ m : Nat, FourWayHit s → Reach s (Verify.ROperationConnection.initial m) := four_way_to_member
example : ∀ (pre : List Move) (m : Nat), FourWayHit (groupRun pre originalStart) → ∃ tail : List Move, groupRun (pre++tail) originalStart = Verify.ROperationConnection.initial m := prefix_four_way_to_member
example : ∀ (pre : List Move) (m : Nat), FourWayHit (groupRun pre originalStart) → ∃ tail : List Move, groupRun (pre++tail) originalStart = Verify.ROperationConnection.initial m ∧ groupRun (Verify.AK3D3BranchConnection.inverseMoves (pre++tail)) (Verify.ROperationConnection.initial m) = originalStart := prefix_four_way_both_directions
end Reviewer007

#print axioms Verify.Submission.EFamily.run_first_Y
#print axioms Verify.Submission.EFamily.run_second_Y
#print axioms Verify.Submission.EFamily.run_second_y
#print axioms Verify.Submission.EFamily.prefix_run
#print axioms Verify.Submission.EFamily.first_mix
#print axioms Verify.Submission.EFamily.second_conjugations
#print axioms Verify.Submission.EFamily.second_mix
#print axioms Verify.Submission.EFamily.restore_second
#print axioms Verify.Submission.EFamily.suffix_run
#print axioms Verify.Submission.EFamily.reaches
#print axioms Verify.Submission.EFamily.word_length
#print axioms Verify.Submission.EFamily.canonical_reaches
#print axioms Verify.Submission.EFamily.zero_initial
#print axioms Verify.Submission.Connections.bridge42_length
#print axioms Verify.Submission.Connections.bridge42_reaches
#print axioms Verify.Submission.Connections.bridge42_cap
#print axioms Verify.Submission.Connections.bridge42_attains22
#print axioms Verify.Submission.Connections.ak3_to_S
#print axioms Verify.Submission.Connections.S_to_ak3
#print axioms Verify.Submission.Connections.ak3_target_iff
#print axioms Verify.Submission.Connections.S_standard_iff_hit
#print axioms Verify.Submission.Connections.member_standard
#print axioms Verify.Submission.Connections.E_standard
#print axioms Verify.Submission.Connections.S_member_iff_standard
#print axioms Verify.Submission.Connections.S_E_iff_standard
#print axioms Verify.Submission.Connections.ak3_E_iff_hit
#print axioms Verify.Submission.Connections.ak3_member_iff_hit
#print axioms Verify.Submission.SixMixFinite.identity_profiles
#print axioms Verify.Submission.SixMixFinite.negative_identity_profiles
#print axioms Verify.Submission.SixMixFinite.viable_layouts
#print axioms Verify.Submission.SixMixFinite.residual_layouts
#print axioms Verify.Submission.SixMixFinite.residual_identity_profiles
#print axioms Verify.Submission.SixMixFinite.residual_negative_profiles
#print axioms Verify.Submission.SixMixFinite.residual_names
