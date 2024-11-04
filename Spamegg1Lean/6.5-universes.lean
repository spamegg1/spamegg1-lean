#check Prop -- Type
#check Type -- Type 1
#check Type 0 -- Type 1
#check Type 1 -- Type 2
#check Type 2 -- Type 3

-- Type is actually Type 0

#check Type -> Type -- Type 1
-- if return type is Prop then the whole function type is Prop:
#check (n : Nat) → n = n + 0 -- Prop (there is a universal quantifier)

inductive MyList0 (α : Type) : Type where
  | nil  : MyList0 α
  | cons : α → MyList0 α → MyList0 α

-- the result would be Type 2, but above def says result is Type 1
-- def myListOfNat : MyList0 Type := .cons Nat .nil

-- also does not work: wrong universe level
-- inductive MyList (α : Type 1) : Type where
--   | nil : MyList α
--   | cons : α → MyList α → MyList α -- universe level 2

-- universe polymorphism: can be used at any universe level
inductive MyList (α : Type u) : Type u where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

-- now these work! it even contains itself (no paradox! just higher level)
def myListOfNumbers : MyList Nat := .cons 0 (.cons 1 .nil)
def myListOfNat : MyList Type := .cons Nat .nil
def myListOfList : MyList (Type → Type) := .cons MyList .nil

-- written with explicit ranks
def myListOfNumbers0 : MyList.{0} Nat := .cons 0 (.cons 1 .nil)
def myListOfNat1 : MyList.{1} Type := .cons Nat .nil
def myListOfList1 : MyList.{1} (Type → Type) := .cons MyList.{0} .nil

-- provide rank arguments for maximum flexibility
inductive MySum (α : Type u) (β : Type u) : Type u where
  | inl : α → MySum α β
  | inr : β → MySum α β

def stringOrNat : Sum String Nat := .inl "hello"
def typeOrType : Sum Type Type := .inr Nat -- can be used at any level

-- even more flexible: different rank variables
inductive Summ (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Summ α β
  | inr : β → Summ α β

def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]

-- Prop is Type, rank 0
def someTruePropositions0 : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]

-- actually, Prop = Sort 0, Type u = Sort (u+1)
