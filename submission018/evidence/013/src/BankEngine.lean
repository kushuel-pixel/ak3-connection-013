import CompactEngine

namespace AK3Bank
open AK3BallEngine (State)
open AK3Compact (Key Ban Table encode children)

/-- Empty cells contain zero; the overflow set can store every key, including zero.
    Collisions always continue to the next bank. -/
inductive Store where
  | last (spill : Table)
  | row (salt width : Nat) (cells : Array Nat) (rest : Store)

/-- Mixing affects performance only. Store lookups compare complete keys. -/
def addr (salt width k : Nat) : Nat :=
  let x := hash k + hash salt + 0x9e3779b97f4a7c15
  let y := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (y ^^^ (y >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31)).toNat % width

def readSlot (cells : Array Nat) (i : Nat) : Nat := cells[i]?.getD 0

def has : Store → Key → Bool
  | .last t, k => t.contains k
  | .row salt n cells rest, k => (k != 0 && readSlot cells (addr salt n k) == k) || has rest k

def put : Store → Key → Store
  | .last t, k => .last (t.insert k)
  | .row salt n cells rest, k =>
    let i := addr salt n k
    if h : i < cells.size then
      if k != 0 && cells[i] == 0 then .row salt n (cells.set i k) rest
      else .row salt n cells (put rest k)
    else .row salt n cells (put rest k)

def every (p : Key → Bool) : Store → Bool
  | .last t => t.all p
  | .row _ _ cells rest => cells.all (fun k => k == 0 || p k) && every p rest

def empty : List Nat → Store
  | [] => .last ∅
  | n::ns => .row n n (Array.replicate n 0) (empty ns)

structure Layer where
  seen : Store
  front : List Key

def add (b : Layer) (j : Key) := if has b.seen j then b else ⟨put b.seen j, j :: b.front⟩

def visit (ban : Ban) (cap : Nat) (b : Layer) (k : Key) : Layer :=
  (children ban cap k).foldl add b

def advance (ban : Ban) (cap : Nat) (b : Layer) : Layer :=
  b.front.foldl (visit ban cap) ⟨b.seen, []⟩

def ball (ns : List Nat) (ban : Ban) (cap : Nat) (s : State) : Nat → Layer
  | 0 => let k := encode s; ⟨put (empty ns) k, [k]⟩
  | r+1 => advance ban cap (ball ns ban cap s r)

def separate (ns : List Nat) (ban : Ban) (cap r t : Nat) (a b : State) : Bool :=
  let left := (ball ns ban cap a r).seen
  let right := (ball ns ban cap b t).seen
  every (fun k => !has right k) left

end AK3Bank
