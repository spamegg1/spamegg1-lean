#check (IO.println)
#check @IO.println

-- brackets are instances, (α : Type) is implicit and can be omitted
def List.sum (α : Type) [Add α] [OfNat α 0] : List α → α
  | []      => 0
  | x :: xs => x + xs.sum

def fourNats : List Nat := [1, 2, 3, 4]
#eval fourNats.sum -- 10

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

#check @OfNat.ofNat

-- Even Number Literals
-- Write an instance of OfNat for the even number datatype from the previous
-- section's exercises that uses recursive instance search.
-- For the base instance, it is necessary to write
-- OfNat Even Nat.zero instead of OfNat Even 0.
inductive Even where
  | zero : Even
  | succ : Even -> Even

def Even.toNat : Even → Nat
  | Even.zero   => 0
  | Even.succ e => e.toNat + 2

def Even.add : Even -> Even -> Even
  | Even.zero, e     => e
  | Even.succ e1, e2 => Even.succ (Even.add e1 e2)

def Even.dbl : Even -> Even
  | Even.zero   => Even.zero
  | Even.succ e => Even.succ (Even.succ (Even.dbl e))

def Even.mul : Even -> Even -> Even
  | Even.zero, _     => Even.zero
  | Even.succ e1, e2 => Even.add (Even.mul e1 e2) (Even.dbl e2)

instance : ToString Even where
  toString x := toString (x.toNat)

instance : Add Even where
  add := Even.add

instance : Mul Even where
  mul := Even.mul

instance : OfNat Even n where
  ofNat :=
    let rec natPlusOne : Nat → Even
      | 0     => Even.zero
      | k + 1 => Even.succ (natPlusOne k)
    natPlusOne n

def even : Even := 8
#eval even -- 16

-- Recursive Instance Search Depth
-- There is a limit to how many times the Lean compiler will
-- attempt a recursive instance search. This places a limit on the size
-- of even number literals defined in the previous exercise.
-- Experimentally determine what the limit is.
