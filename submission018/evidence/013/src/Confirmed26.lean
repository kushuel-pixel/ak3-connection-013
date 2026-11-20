import Confirmed24
import BankSound
import Cap26Compute
namespace Candidate.AK3Peak.FixedS

theorem cap26_ordinary_cut : OrdinaryCut 26 16 24 :=
  CompactSound.ordinary_of_check (BankSound.to_compact cap26_r16_r24)

private theorem upper25_matches_cut {h top r t : Nat} (lo : 25 ≤ h) (hi : h ≤ top)
    (hc : OrdinaryCut top r t) (hsum : r+t = 40) :
    Exact (Witness h ak3 source) 41 ∧ Exact (AvoidWitness h ak3 source) 41 := by
  obtain ⟨hl,_,⟨he,hp⟩,ha⟩ := bypass25_ok
  have w : Witness h ak3 source bypass25 := ⟨he,hp.trans lo⟩
  have lower (ms) (ww : Witness h ak3 source ms) : 41 ≤ ms.length := by
    have hh := lower_of_cut hc (ms := ms) ⟨ww.1,ww.2.trans hi⟩
    omega
  exact ⟨⟨⟨bypass25,hl,w⟩,lower⟩, ⟨⟨bypass25,hl,w,ha⟩, fun ms y => lower ms y.1⟩⟩

theorem exact25_to26 {h : Nat} (lo : 25 ≤ h) (hi : h ≤ 26) :
    Exact (Witness h ak3 source) 41 ∧ Exact (AvoidWitness h ak3 source) 41 :=
  upper25_matches_cut lo hi cap26_ordinary_cut rfl

theorem through30_of_last_cut (h30 : OrdinaryCut 30 16 24) :
    ∀ h, 25 ≤ h → h ≤ 30 → Exact (Witness h ak3 source) 41 ∧ Exact (AvoidWitness h ak3 source) 41 :=
  fun _ lo hi => upper25_matches_cut lo hi h30 rfl

theorem forty_requires_27 {ms : List Verify.AtomicSemantics.Move}
    (he : Verify.AtomicSemantics.wordRun ms ak3 = source) (hlen : ms.length ≤ 40) : 27 ≤ peak ms ak3 := by
  by_contra! low
  have hn := (exact25_to26 (h := 26) (by decide) le_rfl).1.2 ms ⟨he,by omega⟩
  omega

theorem forty_requires_31_of_cut (h30 : OrdinaryCut 30 16 24) {ms : List Verify.AtomicSemantics.Move}
    (he : Verify.AtomicSemantics.wordRun ms ak3 = source) (hlen : ms.length ≤ 40) : 31 ≤ peak ms ak3 := by
  by_contra! low
  have hn := lower_of_cut h30 (ms := ms) ⟨he, by omega⟩
  omega

end Candidate.AK3Peak.FixedS
