import ThroughEdge
import Confirmed24

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

def crosses (s t : WordState) : Prop := (s = U ∧ t = V) ∨ (s = V ∧ t = U)

theorem allowed_false_iff (s t : WordState) : allowed s t = false ↔ crosses s t := by
  simp [allowed,crosses]
  tauto

theorem crossing_of_failed_avoidance {s : WordState} {ms : List Move} (h : avoids ms s = false) :
    ∃ pre m post, ms = pre ++ m::post ∧ crosses (wordRun pre s) (wordStep m (wordRun pre s)) := by
  induction ms generalizing s with
  | nil => simp [avoids] at h
  | cons m ms ih =>
    by_cases hc : allowed s (wordStep m s) = false
    · exact ⟨[],m,ms,rfl,(allowed_false_iff _ _).mp hc⟩
    · have ht : avoids ms (wordStep m s) = false := by
        simpa [avoids,Bool.eq_true_of_not_eq_false hc] using h
      obtain ⟨pre,n,post,he,hh⟩ := ih ht
      exact ⟨m::pre,n,post,by simp [he],hh⟩

/-- This extends forced traversal from the old shortest paths to every path through length 43. -/
theorem compulsory_through_43 {ms : List Move} (w : Witness 22 ak3 source ms) (len : ms.length ≤ 43) :
    ∃ pre m post, ms = pre ++ m::post ∧ crosses (wordRun pre ak3) (wordStep m (wordRun pre ak3)) := by
  apply crossing_of_failed_avoidance
  cases h : avoids ms ak3 with
  | false => rfl
  | true => have hn := exact22_deleted.2 ms ⟨w,h⟩; omega

end Candidate.AK3Peak.FixedS
