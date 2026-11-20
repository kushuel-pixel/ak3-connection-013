import FixedSWitness

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

def labels : List Move := [.m0,.m1,.m2,.m3,.m4,.m5,.m6,.m7,.m8,.m9,.m10,.m11,.m12,.m13]
theorem labels_complete (m : Move) : m ∈ labels := by cases m <;> decide +kernel
theorem labels_distinct : labels.Nodup := by decide +kernel

abbrev Counts := List (WordState × Nat)
def ways (t : Counts) (s : WordState) : Nat :=
  match t with
  | [] => 0
  | (v,k)::rest => if s = v then k else ways rest s

/-- Number of ordered suffixes staying in the indicated next layers.
    The last move must end at the fixed target. -/
def countFrom (cap : Nat) : List (List WordState) → WordState → Nat
  | [], s => if total s ≤ cap ∧ s = source then 1 else 0
  | layer::layers, s =>
    if total s ≤ cap then
      (labels.map fun m => let v := wordStep m s
                           if v ∈ layer then countFrom cap layers v else 0).sum
    else 0

def propagate (cap : Nat) (layer : List WordState) (tails : Counts) : Counts :=
  layer.map fun s => (s, if total s ≤ cap then
    (labels.map fun m => ways tails (wordStep m s)).sum else 0)

def table (cap : Nat) : List (List WordState) → Counts
  | [] => []
  | [layer] => layer.map fun s => (s, countFrom cap [] s)
  | layer::next::rest =>
    propagate cap layer (table cap (next::rest))

private theorem ways_map (layer : List WordState) (f : WordState → Nat) (s : WordState) :
    ways (layer.map fun v => (v,f v)) s = if s ∈ layer then f s else 0 := by
  induction layer with
  | nil => simp [ways]
  | cons a xs ih =>
    by_cases he : s = a <;> simp [ways,he,ih]

/-- The fast suffix table computes exactly the branching recurrence on the listed layers. -/
theorem table_correct (cap : Nat) (layer : List WordState) (rest : List (List WordState)) (s : WordState) :
    ways (table cap (layer::rest)) s = if s ∈ layer then countFrom cap rest s else 0 := by
  induction rest generalizing layer s with
  | nil =>
    simp only [table, ways_map]
  | cons next tail ih =>
    rw [table, propagate, ways_map]
    simp only [countFrom]
    simp only [ih]

end Candidate.AK3Peak.FixedS
