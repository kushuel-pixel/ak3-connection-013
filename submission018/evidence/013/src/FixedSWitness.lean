import B5Bridge42

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

/-- Literal freely reduced words use the alphabet of the published certificates. -/
macro "w!" s:str : term => do
  let letters ← s.getString.toList.mapM fun c => do
    match c with
    | 'x' => `(Verify.ReducedWords.xLetter)
    | 'X' => `(Verify.ReducedWords.XLetter)
    | 'y' => `(Verify.ReducedWords.yLetter)
    | 'Y' => `(Verify.ReducedWords.YLetter)
    | _ => Lean.Macro.throwError "expected x, X, y or Y"
  `([$letters.toArray,*])

def U : WordState := (w! "xYYYYXyyy", w! "yyxxYX")
def V : WordState := (w! "xYYYYXyyy", w! "yyxxYYYYYXyyy")

/-- Both orientations of this literal edge are forbidden. -/
def allowed (s t : WordState) : Bool :=
  !((s == U && t == V) || (s == V && t == U))

def avoids : List Move → WordState → Bool
  | [], _ => true
  | m :: ms, s => allowed s (wordStep m s) && avoids ms (wordStep m s)

def AvoidWitness (cap : Nat) (s t : WordState) (ms : List Move) : Prop :=
  Witness cap s t ms ∧ avoids ms s = true

/-- Explicit intermediate states avoid repeatedly reducing long prefixes in the kernel. -/
abbrev Rows := List (Move × WordState)

def traceOK : WordState → Rows → Bool
  | _, [] => true
  | s, (m,t) :: rs => (wordStep m s == t) && traceOK t rs

def finish : WordState → Rows → WordState
  | s, [] => s
  | _, (_,t) :: rs => finish t rs

def height : WordState → Rows → Nat
  | s, [] => total s
  | s, (_,t) :: rs => max (total s) (height t rs)

def clearEdges : WordState → Rows → Bool
  | _, [] => true
  | s, (_,t) :: rs => allowed s t && clearEdges t rs

theorem trace_sound {s : WordState} {rs : Rows} (ok : traceOK s rs = true) :
    wordRun (rs.map Prod.fst) s = finish s rs ∧
    peak (rs.map Prod.fst) s = height s rs ∧
    avoids (rs.map Prod.fst) s = clearEdges s rs := by
  induction rs generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons row rs ih =>
    obtain ⟨m,t⟩ := row
    simp only [traceOK, Bool.and_eq_true, beq_iff_eq] at ok
    obtain ⟨he,hp,hc⟩ := ih ok.2
    simp only [List.map_cons, wordRun, peak, avoids, finish, height, clearEdges, ok.1, he, hp, hc,
      and_self]

theorem certified {s t : WordState} {n cap : Nat} (rs : Rows)
    (h : traceOK s rs = true ∧ finish s rs = t ∧ height s rs = cap ∧
      clearEdges s rs = true ∧ rs.length = n) :
    (rs.map Prod.fst).length = n ∧ peak (rs.map Prod.fst) s = cap ∧
    AvoidWitness cap s t (rs.map Prod.fst) := by
  obtain ⟨ok, hf, hh, hc, hn⟩ := h
  obtain ⟨he, hp, ha⟩ := trace_sound ok
  exact ⟨by simpa using hn, hp.trans hh, ⟨he.trans hf, (hp.trans hh).le⟩, ha.trans hc⟩

end Candidate.AK3Peak.FixedS
