-- Boolean equality with ==
#check 2 == 2 -- : Bool
#eval 2 == 2 -- true

-- mathematical equality with =, it has type Prop
#check 2 = 2 -- : Prop
#eval 2 = 2 -- : true

-- this is an undecidable statement, so it gives error "failed to syntesize Decidable"
-- #eval if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no" -- error

-- built-in ordering typeclass
-- inductive Ordering where
-- | lt
-- | eq
-- | gt

-- Pos from before
inductive Pos : Type where
  | one  : Pos
  | succ : Pos → Pos

-- instance of comparison / ordering for Pos
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one       => Ordering.eq
  | Pos.one, Pos.succ _    => Ordering.lt
  | Pos.succ _, Pos.one    => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp

-- like Java's hashcode
-- class Hashable (α : Type) where
--   hash : α → UInt64

def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

-- from before
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}
instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

-- binary tree
inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1 (mixHash (hashBinTree left) (mixHash (hash x) (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

-- deriving instead of implementing
deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable, Repr for NonEmptyList

-- appending typeclass
-- class HAppend (α : Type) (β : Type) (γ : outParam Type) where
--   hAppend : α → β → γ

instance : Append (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys := { head := xs.head, tail := xs.tail ++ ys }

#eval idahoSpiders ++ ["Trapdoor Spider"]

-- FUNCTORS: need to implement map
#eval Functor.map (· + 5) [1, 2, 3] -- 678
#eval (· + 5) <$> [1, 2, 3] -- alternative infix notation
#eval Functor.map toString (some (List.cons 5 List.nil)) -- some "[5]"
#eval Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]

instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }

-- from before
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | []        => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail

-- class Functor (f : Type → Type) where
--   map : {α β : Type} → (α → β) → f α → f β

--   mapConst {α β : Type} (x : α) (coll : f β) : f α :=
--     map (fun _ => x) coll

-- Write an instance of HAppend (List α) (NonEmptyList α) (NonEmptyList α) and test it.
def neHappend : (List α) -> (NonEmptyList α) -> (NonEmptyList α)
| List.nil, ys                     => ys
| x :: xs, {head := y, tail := ys} => {head := x, tail := xs ++ (y :: ys)}

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend := neHappend

def fourFiveSix : NonEmptyList Nat := { head := 4, tail := [5, 6] }
#eval [1, 2, 3] ++ fourFiveSix -- h:1, t:23456

-- Implement a Functor instance for the binary tree datatype. Definitions:
-- inductive BinTree (α : Type) where
--   | leaf   : BinTree α
--   | branch : BinTree α → α → BinTree α → BinTree α
-- class Functor (f : Type → Type) where
--   map : {α β : Type} → (α → β) → f α → f β
def btMap {α β : Type} : (α → β) → BinTree α → BinTree β
| _, BinTree.leaf         => BinTree.leaf
| f, BinTree.branch l x r => BinTree.branch (btMap f l) (f x) (btMap f r)

instance : Functor BinTree where
  map := btMap

def bt : BinTree Nat := BinTree.branch (BinTree.leaf) 5 (BinTree.leaf)
#eval (. ^ 2) <$> bt
