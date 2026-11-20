import CompactSound
import Cap22Compute
import Cap24Compute

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

theorem cap22_deleted_cut : DeletedCut 22 17 26 := CompactSound.deleted_of_check cap22_r17_r26
theorem cap24_ordinary_cut : OrdinaryCut 24 15 26 := CompactSound.ordinary_of_check cap24_r15_r26

theorem exact22_deleted : Exact (AvoidWitness 22 ak3 source) 44 := deleted22_of_cut cap22_deleted_cut

theorem exact22_to24 {h : Nat} (lo : 22 ≤ h) (hi : h ≤ 24) : Exact (Witness h ak3 source) 42 := by
  exact ⟨⟨Bridge42.forward, Bridge42.lengths.1, Bridge42.forward_ok.1, Bridge42.forward_ok.2.trans lo⟩,
    fun ms w => lower_of_cut cap24_ordinary_cut (ms := ms) ⟨w.1,w.2.trans hi⟩⟩

theorem exact23_to24_deleted {h : Nat} (lo : 23 ≤ h) (hi : h ≤ 24) :
    Exact (AvoidWitness h ak3 source) 42 := by
  obtain ⟨hl,_,⟨he,hp⟩,ha⟩ := bypass23_ok
  exact ⟨⟨bypass23,hl,⟨he,hp.trans lo⟩,ha⟩,
    fun ms w => (exact22_to24 (by omega : 22 ≤ h) hi).2 ms w.1⟩

/-- Cap 25 is necessary and sufficient for any path of at most 41 moves. -/
theorem reachable_in_41_iff (h : Nat) :
    (∃ ms : List Move, ms.length ≤ 41 ∧ Witness h ak3 source ms) ↔ 25 ≤ h := by
  constructor
  · intro ⟨ms,hl,w⟩
    by_contra! small
    have bound : 42 ≤ ms.length := (exact22_to24 (h := 24) (by decide) le_rfl).2 ms
      ⟨w.1,w.2.trans (by omega)⟩
    omega
  · intro hh
    obtain ⟨hl,_,⟨he,hp⟩,_⟩ := bypass25_ok
    exact ⟨bypass25,hl.le,he,hp.trans hh⟩

end Candidate.AK3Peak.FixedS
