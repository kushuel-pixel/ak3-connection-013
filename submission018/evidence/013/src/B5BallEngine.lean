import Std.Data.HashSet.Basic

namespace AK3BallEngine

abbrev Letter := Fin 2 × Bool
abbrev Word := List Letter
abbrev State := Word × Word
def xLetter : Letter := (0, true)
def XLetter : Letter := (0, false)
def yLetter : Letter := (1, true)
def YLetter : Letter := (1, false)
def digit (a : Letter) : Nat := 2 * a.1.val + (if a.2 then 0 else 1)

def letter : Nat → Letter
  | 0 => xLetter | 1 => XLetter | 2 => yLetter | _ => YLetter

def pack : Word → Nat
  | [] => 1
  | a :: w => 4 * pack w + digit a

def unpack (n : Nat) : Word :=
  if h : n < 4 then [] else letter (n % 4) :: unpack (n / 4)
termination_by n
decreasing_by omega

abbrev Key := Nat × Nat
abbrev Table := Std.HashSet Key

def encode (s : State) : Key := (pack s.1, pack s.2)
def decode (k : Key) : State := (unpack k.1, unpack k.2)

def inverse (w : Word) : Word := (w.map fun g => (g.1, !g.2)).reverse

def reduce : Word → Word
  | [] => []
  | a :: w => match reduce w with
    | [] => [a]
    | b :: rest => if a.1 = b.1 ∧ a.2 = !b.2 then rest else a :: b :: rest

def conj (a : Letter) (w : Word) := reduce ([a] ++ w ++ inverse [a])

def step : Nat → State → State
  | 0, (a,b) => (inverse a, b)
  | 1, (a,b) => (a, inverse b)
  | 2, (a,b) => (reduce (a ++ b), b)
  | 3, (a,b) => (reduce (a ++ inverse b), b)
  | 4, (a,b) => (a, reduce (b ++ a))
  | 5, (a,b) => (a, reduce (b ++ inverse a))
  | 6, (a,b) => (conj xLetter a, b)
  | 7, (a,b) => (conj XLetter a, b)
  | 8, (a,b) => (conj yLetter a, b)
  | 9, (a,b) => (conj YLetter a, b)
  | 10, (a,b) => (a, conj xLetter b)
  | 11, (a,b) => (a, conj XLetter b)
  | 12, (a,b) => (a, conj yLetter b)
  | _, (a,b) => (a, conj YLetter b)

def moveIds := List.range 14

def children (cap : Nat) (k : Key) : List Key :=
  let s := decode k
  moveIds.filterMap fun m =>
    let t := step m s
    if t.1.length + t.2.length ≤ cap then some (encode t) else none

structure Layer where
  seen : Table
  front : Table

def extend (cap : Nat) (b : Layer) : Layer :=
  let hits := b.front.fold (fun acc k => acc.insertMany (children cap k)) (∅ : Table)
  let fresh := hits \ b.seen
  ⟨b.seen ∪ fresh, fresh⟩

def ball (cap : Nat) (s : State) : Nat → Layer
  | 0 => let root := (∅ : Table).insert (encode s); ⟨root, root⟩
  | n+1 => extend cap (ball cap s n)

def separate (cap r t : Nat) (a b : State) : Bool :=
  let left := (ball cap a r).seen
  let right := (ball cap b t).seen
  left.all (fun k => !right.contains k)

end AK3BallEngine
