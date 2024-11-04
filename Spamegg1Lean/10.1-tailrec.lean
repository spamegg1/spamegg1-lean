def NonTail.sum : List Nat → Nat
  | []      => 0
  | x :: xs => x + sum xs

def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | []      => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat := Tail.sumHelper 0 xs

#eval Tail.sum [1, 2, 3]

def NonTail.reverse : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

def Tail.reverseHelper (soFar : List α) : List α → List α
  | []      => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α := Tail.reverseHelper [] xs

inductive BinTree (α : Type) where -- from before
  | leaf   : BinTree α
  | branch : BinTree α -> α -> BinTree α -> BinTree α
deriving Repr

-- Cannot be straightforwardly rewritten to be TR using accumulator-passing style.
-- ∃ techniques for making these TR, such as using continuation-passing style.
def BinTree.mirror : BinTree α → BinTree α
  | .leaf         => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

-- Translate each of the following non-tail-recursive functions
-- into accumulator-passing tail-recursive functions:
def NonTail.length : List α → Nat
  | []      => 0
  | _ :: xs => NonTail.length xs + 1

def NonTail.factorial : Nat → Nat
  | 0     => 1
  | n + 1 => factorial n * (n + 1)

def Tail.lengthHelper : List α → Nat → Nat
  | [], acc      => acc
  | _ :: xs, acc => lengthHelper xs (acc + 1)

def Tail.length (xs : List α) : Nat := Tail.lengthHelper xs 0
#eval Tail.length [1, 2, 3, 4, 5]

def Tail.factorialHelper : Nat → Nat → Nat
  | 0, acc     => acc
  | n + 1, acc => factorialHelper n (acc * (n + 1))

def Tail.factorial (n : Nat) : Nat := Tail.factorialHelper n 1
#eval Tail.factorial 5

-- The translation of NonTail.filter should result in a program that takes constant stack
-- space through tail recursion, and time linear in the length of the input list.
-- A constant factor overhead is acceptable relative to the original:
def NonTail.filter (p : α → Bool) : List α → List α
  | []      => []
  | x :: xs => if p x then x :: filter p xs else filter p xs

def Tail.filterHelper (p : α → Bool) : List α → List α → List α
  | [], acc      => acc.reverse
  | x :: xs, acc => filterHelper p xs (if p x then x :: acc else acc)

def Tail.filter (p : α → Bool) (xs : List α) : List α := Tail.filterHelper p xs []
#eval Tail.filter (. % 2 = 1) [1, 2, 3, 4, 5]
