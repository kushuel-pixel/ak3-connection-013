import Adjacent.Transport

/-! Keep the second relator at the endpoints. During the path it may be conjugated
by powers of y. Every output letter is one existing ac-r2-v1 ID. -/
namespace Verify.OneRelatorEntry

open AtomicSemantics ResearchWords
open SevenPrefixUpperBound (groupRun_append)

def substitute (a b : F) : F →* F :=
  FreeGroup.lift fun i : Fin 2 => if i = 0 then a else b

@[simp] private theorem sub_x (a b : F) : substitute a b x = a := by
  simp [substitute, x]
@[simp] private theorem sub_y (a b : F) : substitute a b y = b := by
  simp [substitute, y]

@[simp] private theorem empty_word : (FreeGroup.mk ([] : Word)) = 1 := rfl

private def moveOf (l : Letter) : Move :=
  if l.1 = 0 then (if l.2 then .m2 else .m3)
  else (if l.2 then .m12 else .m13)

def scan (w : Word) : List Move := w.map moveOf

private def frame (a b q : F) : GroupState := (a*q⁻¹,q*b*q⁻¹)

private theorem one_letter (a b q : F) (l : Letter) (hq : Commute y q) :
    groupStep (moveOf l) (frame a b q) =
      frame (a * substitute b y (FreeGroup.mk [l])) b (q * substitute 1 y (FreeGroup.mk [l])) := by
  have hy := hq.eq
  have hi := hq.inv_left.eq
  rcases l with ⟨i,s⟩
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> cases s
  · change (a*q⁻¹*(q*b*q⁻¹)⁻¹,_) = frame (a*substitute b y x⁻¹) b (q*substitute 1 y x⁻¹)
    simp [frame, mul_assoc]
  · change (a*q⁻¹*(q*b*q⁻¹),_) = frame (a*substitute b y x) b (q*substitute 1 y x)
    simp [frame, mul_assoc]
  · change (_,Y * (q*b*q⁻¹)*y) = frame (a * substitute b y y⁻¹) b (q * substitute 1 y y⁻¹)
    simp only [map_inv, sub_y, frame, Y, mul_inv_rev, inv_inv]
    apply Prod.ext
    · simp [mul_assoc]
    · change y⁻¹*(q*b*q⁻¹)*y = (q*y⁻¹)*b*(y*q⁻¹)
      rw [← hi]
      simp only [mul_assoc, hq.inv_right.eq]
  · change (_,y * (q*b*q⁻¹)*Y) = frame (a * substitute b y y) b (q * substitute 1 y y)
    simp only [sub_y, frame, Y, mul_inv_rev]
    apply Prod.ext
    · simp [mul_assoc]
    · change y*(q*b*q⁻¹)*y⁻¹ = (q*y)*b*(y⁻¹*q⁻¹)
      rw [← hy]
      simp only [mul_assoc, hq.inv_left.inv_right.eq]

private theorem remove_x_commutes (w : Word) : Commute y (substitute 1 y (FreeGroup.mk w)) := by
  induction w with
  | nil => simp [empty_word]
  | cons l rest ih =>
    change Commute y (substitute 1 y (FreeGroup.mk [l] * FreeGroup.mk rest))
    rw [map_mul]
    apply Commute.mul_right _ ih
    rcases l with ⟨i,s⟩
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> cases s
    · change Commute y (substitute 1 y x⁻¹)
      simp
    · change Commute y (substitute 1 y x)
      simp
    · change Commute y (substitute 1 y y⁻¹)
      simp
    · change Commute y (substitute 1 y y)
      simp

private theorem scan_from (w : Word) (a b q : F) (hq : Commute y q) :
    groupRun (scan w) (frame a b q) =
      frame (a * substitute b y (FreeGroup.mk w)) b (q * substitute 1 y (FreeGroup.mk w)) := by
  induction w generalizing a q with
  | nil => simp [scan, groupRun, empty_word]
  | cons l rest ih =>
    change groupRun (scan rest) (groupStep (moveOf l) (frame a b q)) = _
    rw [one_letter _ _ _ _ hq, ih _ _ (hq.mul_right (remove_x_commutes [l]))]
    change _ = frame (a * substitute b y (FreeGroup.mk [l] * FreeGroup.mk rest)) b
      (q * substitute 1 y (FreeGroup.mk [l] * FreeGroup.mk rest))
    simp only [map_mul,mul_assoc]

/-- In the alphabet (b,y), any correction with zero y exponent can be
multiplied onto the first relator at cost one existing move per letter. -/
theorem scan_closed (a b : F) (w : Word) (closed : substitute 1 y (FreeGroup.mk w) = 1) :
    groupRun (scan w) (a,b) = (a * substitute b y (FreeGroup.mk w), b) := by
  simpa [frame, closed] using (scan_from w a b 1 (Commute.one_right _))

theorem scan_length (w : Word) : (scan w).length = w.length := by simp [scan]

end Verify.OneRelatorEntry
