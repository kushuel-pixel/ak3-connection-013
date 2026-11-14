import Submission.SixMixFinite
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
example : Verify.Submission.SixMixFinite.count Verify.Submission.SixMixFinite.unit = 243 := by decide +kernel
