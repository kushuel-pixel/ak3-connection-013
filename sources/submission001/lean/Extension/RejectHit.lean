import Extension.Audit
open Verify Verify.AtomicSemantics Verify.EntryExtension Verify.EntryExtension.Audit
example : FourWayHit fibBasis := by
  simp only [fixture_not_complete.2]
  decide +kernel
