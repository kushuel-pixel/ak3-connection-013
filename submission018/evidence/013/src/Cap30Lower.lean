import B5BallSearch

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

theorem cap30_r8_r15 : AK3BallEngine.separate 30 8 15 ak3 source = true := by decide +native

theorem cap30_at_least_24 {ms : List Move} (w : Witness 30 ak3 source ms) : 24 ≤ ms.length := by
  by_contra! h
  have hr : ReducedState ak3 := by
    constructor <;> apply FreeGroup.IsReduced.of_reduce_eq <;> decide +kernel
  obtain ⟨u, ha, hb⟩ := Bridge42.witness_split (p := 8) (q := 15) hr w (by omega)
  exact BallSearch.separate_sound cap30_r8_r15 u ha hb

end Candidate.AK3Peak.FixedS
#check Candidate.AK3Peak.FixedS.cap30_at_least_24
#print axioms Candidate.AK3Peak.FixedS.cap30_at_least_24
