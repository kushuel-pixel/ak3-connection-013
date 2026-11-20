import B5BallEngine

namespace AK3Compact
open AK3BallEngine (State Word digit letter pack unpack step)

abbrev Key := Nat
abbrev Ban := Option (Key × Key)
abbrev Table := Std.HashSet Key

/-- Low base-five digits encode the first word. The digit 4 marks the start of
    the old base-four code for the second word. There is no fixed word-length limit. -/
def prepend (w : Word) (tail : Nat) : Nat :=
  match w with
  | [] => tail
  | a :: rest => 5 * prepend rest tail + digit a

def encode (s : State) := prepend s.1 (5 * pack s.2 + 4)

def decode (n : Nat) : State :=
  if n < 5 then ([], []) else
  if n % 5 = 4 then ([], unpack (n / 5)) else
    let (u,v) := decode (n / 5)
    (letter (n % 5) :: u, v)
termination_by n
decreasing_by omega

def permitted (ban : Ban) (k j : Key) : Bool :=
  match ban with
  | none => true
  | some (a,b) => !((k == a && j == b) || (k == b && j == a))

def children (ban : Ban) (cap : Nat) (k : Key) : List Key :=
  let s := decode k
  AK3BallEngine.moveIds.filterMap fun m =>
    let t := step m s
    if t.1.length + t.2.length ≤ cap then
      let j := encode t
      if permitted ban k j then some j else none
    else none

structure Layer where
  seen : Table
  front : List Key

def add (b : Layer) (j : Key) : Layer :=
  if j ∈ b.seen then b else ⟨b.seen.insert j, j :: b.front⟩

def visit (ban : Ban) (cap : Nat) (b : Layer) (k : Key) : Layer :=
  (children ban cap k).foldl add b

def advance (ban : Ban) (cap : Nat) (b : Layer) : Layer :=
  b.front.foldl (visit ban cap) ⟨b.seen, []⟩

def ball (ban : Ban) (cap : Nat) (s : State) : Nat → Layer
  | 0 => let k := encode s; ⟨(∅ : Table).insert k, [k]⟩
  | r+1 => advance ban cap (ball ban cap s r)

def separate (ban : Ban) (cap r t : Nat) (a b : State) : Bool :=
  let left := (ball ban cap a r).seen
  let right := (ball ban cap b t).seen
  left.all (fun k => !right.contains k)
end AK3Compact
