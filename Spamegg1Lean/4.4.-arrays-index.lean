def northernTrees : Array String := #["sloe", "birch", "elm", "oak"]

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

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0                              => some xs.head
  | {head := _, tail := []},     _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n

def NonEmptyList.get2? : NonEmptyList α → Nat → Option α
  | xs, 0     => some xs.head
  | xs, n + 1 => xs.tail.get? n

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide
theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by decide

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (_ : xs.inBounds i) : α :=
  match i with
  | 0     => xs.head
  | n + 1 => xs.tail[n]

class MyGetElem
  (coll : Type)
  (idx : Type)
  (item : outParam Type)
  (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

-- #eval idahoSpiders[9] -- failed to prove index is valid

-- Pos structure from before
inductive Pos : Type where
  | one  : Pos
  | succ : Pos → Pos

-- instance : OfNat Pos (n + 1) where
--   ofNat :=
--     let rec natPlusOne : Nat → Pos
--       | 0     => Pos.one
--       | k + 1 => Pos.succ (natPlusOne k)
--     natPlusOne n

def Pos.toNat : Pos → Nat
  | Pos.one    => 1
  | Pos.succ n => n.toNat + 1

-- instance : ToString Pos where
--   toString x := toString (x.toNat)

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]

-- PPoint from before
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y
