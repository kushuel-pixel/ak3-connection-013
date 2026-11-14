import Std

/-! Kernel-evaluated finite matrix inventory only. The interpretation of an
arbitrary original AC path and the quotient obstructions are not formalized here. -/
namespace Verify.Submission.SixMixFinite
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

structure Mat where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, BEq, Repr
def unit : Mat := ⟨1,0,0,1⟩
def negUnit : Mat := ⟨-1,0,0,-1⟩
def mul (p q : Mat) : Mat :=
  ⟨p.a*q.a+p.b*q.c,p.a*q.b+p.b*q.d,p.c*q.a+p.d*q.c,p.c*q.b+p.d*q.d⟩
def elementary (first : Bool) (s : Int) : Mat :=
  if first then ⟨1,s,0,1⟩ else ⟨1,0,s,1⟩
def sign (mask i : Nat) : Int := if mask.testBit i then 1 else -1
def product (layout signs : Nat) : Mat :=
  (List.range 6).foldl (fun p i => mul (elementary (layout.testBit i) (sign signs i)) p) unit
def solutions (layout : Nat) (target : Mat) : List Nat :=
  (List.range 64).filter (fun signs => product layout signs == target)
def count (target : Mat) : Nat :=
  ((List.range 64).map (fun layout => (solutions layout target).length)).sum
def viable : List Nat :=
  (List.range 64).filter (fun layout =>
    !(solutions layout unit).isEmpty || !(solutions layout negUnit).isEmpty)
def name (layout : Nat) : String :=
  String.ofList ((List.range 6).map (fun i => if layout.testBit i then 'F' else 'Q'))
def excludedNames : List String :=
  ["FFFFFF","QQQQQQ","FFFFQQ","FFQQQQ","QQFFFF","QQQQFF"]
def residual : List Nat := viable.filter (fun layout => !(excludedNames.contains (name layout)))
def residualCount (target : Mat) : Nat :=
  (residual.map (fun layout => (solutions layout target).length)).sum

theorem identity_profiles : count unit = 244 := by decide +kernel
theorem negative_identity_profiles : count negUnit = 16 := by decide +kernel
theorem viable_layouts : viable.length = 22 := by decide +kernel
theorem residual_layouts : residual.length = 16 := by decide +kernel
theorem residual_identity_profiles : residualCount unit = 156 := by decide +kernel
theorem residual_negative_profiles : residualCount negUnit = 16 := by decide +kernel
theorem residual_names : residual.map name =
  ["QFFQQQ", "FQQFQQ", "QQFFQQ", "QFQQFQ", "FQFQFQ", "QQQFFQ", "FFQFFQ", "QFFFFQ", "FQQQQF", "QQFQQF", "FFFQQF", "QFQFQF", "FQFFQF", "FFQQFF", "QFFQFF", "FQQFFF"] := by
  decide +kernel

end Verify.Submission.SixMixFinite
