import Extension.FourWay
open Verify Verify.AtomicSemantics Verify.EntryExtension
example : Reach (x*x,y) (ROperationConnection.initial 3) := by
  apply four_way_to_member (x*x,y) (by decide +kernel) 3
  exact Or.inr (Or.inr (by decide +kernel))
