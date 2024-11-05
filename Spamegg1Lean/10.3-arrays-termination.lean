-- Lean built-in
-- class LE (α : Type u) where
--   le : α → α → Prop
-- class LT (α : Type u) where
--   lt : α → α → Prop
instance : LE Nat where
  le := Nat.le

-- Inductively-Defined Propositions, Predicates, and Relations
inductive EasyToProve : Prop where
  | heresTheProof : EasyToProve

theorem fairlyEasy : EasyToProve := by constructor

-- Lean built-in
-- inductive True : Prop where
--   | intro : True

inductive IsThree : Nat → Prop where
  | isThree : IsThree 3

theorem three_is_three : IsThree 3 := by constructor

inductive IsFive : Nat → Prop where
  | isFive : IsFive 5

theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => constructor

theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
  cases h

-- Lean built-in
-- inductive Nat.le (n : Nat) : Nat → Prop
--   | refl : Nat.le n n
--   | step : Nat.le n m → Nat.le n (m + 1)

theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step (step (step refl))

-- Lean built-in
-- def Nat.lt (n m : Nat) : Prop :=
--   Nat.le (n + 1) m
instance : LT Nat where
  lt := Nat.lt

theorem four_lt_seven : 4 < 7 :=
  open Nat.le in
  step (step refl)

def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
termination_by arr.size - i -- seems unnecessary in current Lean version

-- Lean built-in
-- def Array.map (f : α → β) (arr : Array α) : Array β :=
--   arrayMapHelper f arr Array.empty 0
def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then some (i, x) else findHelper arr p (i + 1)
  else none
termination_by arr.size - i -- again, this can be commented out without issue.

def Array.find (arr : Array α) (p : α → Bool) : Option (Nat × α) := findHelper arr p 0

-- EXERCISES
-- Implement a ForM (Array α) instance on arrays using a tail-recursive
-- accumulator-passing function and a termination_by clause.
def Array.forMhelper [Monad m] (arr : Array α) (f : α → m PUnit) (i : Nat) : m PUnit :=
  if h : i < arr.size then do
    f arr[i]
    forMhelper arr f (i + 1)
  else pure ()
termination_by arr.size - i -- again, unnecessary

def Array.forM2 [Monad m] (arr : Array α) (f : α → m PUnit) : m PUnit :=
  Array.forMhelper arr f 0
instance : ForM m (Array α) α where forM := Array.forM2

-- Implement a function to reverse arrays using a tail-recursive accumulator-passing
-- function that doesn't need a termination_by clause.
-- NOT SURE HOW TO DO THIS... I think it doesn't need a clause due to newer Lean version.
def Array.reverseHelper (arr : Array α) (acc : List α) (i : Nat) : Array α :=
  if h : i < arr.size then
    reverseHelper arr (arr[i] :: acc) (i + 1)
  else acc.toArray
def Array.reverseTR (arr : Array α) : Array α := Array.reverseHelper arr [] 0
#eval Array.reverseTR #[1, 2, 3]

-- Reimplement Array.map, Array.find, and the ForM instance using for ... in ...
-- loops in the identity monad and compare the resulting code.
def Array.map2 (f : α → β) (arr : Array α) : Array β := Id.run do
  let mut out : Array β := {}
  for x in arr do
    out := out.push (f x)
  out
#eval Array.map2 (. ^ 2) #[1, 2, 3] -- 1 4 9

def Array.find2 (arr : Array α) (p : α → Bool) : Option (Nat × α) := Id.run do
  let mut i : Nat := 0
  for x in arr do
    if h : i < arr.size then
      if p arr[i] then
        return some (i, arr[i])
    i := i + 1
  none

#eval Array.find2 #[1, 3, 5] (. % 2 == 0) -- none
#eval Array.find2 #[3, 4, 6] (. % 2 == 0) -- some (1, 4)

-- Reimplement array reversal using a for ... in ... loop in the identity monad.
-- Compare it to the tail-recursive function.
def Array.reverseFor (arr : Array α) : Array α := Id.run do
  let mut out : List α := []
  for x in arr do
    out := x :: out
  out.toArray -- am I allowed to use this?
#eval Array.reverseFor #[1, 2, 3] -- 3 2 1
