def equal? [BEq α] (x y : α) : Option α := if x == y then some x else none

inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def BinTree.mirror : BinTree α → BinTree α
  | .leaf         => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

def BinTree.empty : BinTree α := .leaf
#check (.empty : BinTree Nat)

inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
  deriving Repr

def Weekday.isWeekend : Weekday -> Bool
  | .saturday | .sunday => true
  | _                   => false

def condense : α ⊕ α → α
  | .inl x | .inr x => x

def stringy : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"It is {repr x}"

-- x, y cannot be used, error, b/c they need to appear in all patterns.
def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, x) | .inr (n, y) => n

-- def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
--   | .inl (n, x) | .inr (n, y) => x -- error

def str := "Some string"

def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (n, str) | .inr (n, y) => str

#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String)) -- twenty
#eval getTheString (.inr (20, "twenty")) -- some string
