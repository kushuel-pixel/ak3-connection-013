import Submission.Connections
import Submission.SixMixFinite
open Verify Verify.AtomicSemantics Verify.EntryExtension
example (s : GroupState) (hit : FourWayHit s) : Reach s (x,y) := four_way_to_standard s hit
