import Extension.FourWay
open Verify Verify.AtomicSemantics Verify.EntryExtension
example : groupRun [.m2] (rows (x,y)) = rows (groupRun [.m2] (x,y)) := by decide +kernel
