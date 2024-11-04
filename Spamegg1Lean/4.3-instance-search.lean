-- from 4.1
inductive Pos : Type where
  | one  : Pos
  | succ : Pos → Pos

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0     => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def Pos.toNat : Pos → Nat
  | Pos.one    => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

def addNatPos : Nat → Pos → Pos
  | 0, p     => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0     => p
  | p, n + 1 => Pos.succ (addPosNat p n)

-- heterogeneous overloading
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)

class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

-- #eval HPlus.hPlus (3 : Pos) (5 : Nat) -- error
#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos) -- OK

-- output parameters
class HPlus2 (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus2 Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus2 Pos Nat Pos where
  hPlus := addPosNat

#eval HPlus2.hPlus (3 : Pos) (5 : Nat) -- works now!

-- default instances
@[default_instance]
instance [Add α] : HPlus2 α α α where
  hPlus := Add.add

#eval HPlus2.hPlus (3 : Nat) (5 : Nat)
#check HPlus.hPlus (5 : Nat)

-- Define an instance of HMul (PPoint α) α (PPoint α)
-- that multiplies both projections by the scalar.
-- It should work for any type α for which there is a Mul α instance. For example,
-- #eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
-- should yield
-- { x := 5.000000, y := 7.400000 }
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def mulPointAlpha [Mul α] : (PPoint α) -> α -> (PPoint α)
  | p, a => PPoint.mk (p.x * a) (p.y * a)

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul := mulPointAlpha

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0 -- { x := 5.000000, y := 7.400000 }
