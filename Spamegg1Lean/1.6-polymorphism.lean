structure PPoint (T : Type) where
  x : T
  y : T
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

def replaceX (T : Type) (point : PPoint T) (newX : T) : PPoint T :=
  { point with x := newX }

#check (replaceX)   -- (T : Type) -> PPoint T   -> T   -> PPoint T
#check replaceX Nat --              PPoint Nat -> Nat -> PPoint Nat

#check replaceX Nat natOrigin   -- Nat -> PPoint Nat
#check replaceX Nat natOrigin 5 --        PPoint Nat
#eval  replaceX Nat natOrigin 5 -- 5,0

inductive Sign where
  | pos
  | neg
deriving Repr

def posOrNegThree (s : Sign)
  : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

#eval posOrNegThree Sign.pos --  3 : Nat
#eval posOrNegThree Sign.neg -- -3 : Int

def primesUnder10 : List Nat := [2, 3, 5, 7]

inductive MyList (T : Type) where
  | nil  : MyList T
  | cons : T -> MyList T -> MyList T

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

def length (T : Type) (xs : List T) : Nat :=
  match xs with
  | List.nil       => Nat.zero
  | List.cons _ ys => Nat.succ (length T ys)

def length2 (T : Type) (xs : List T) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (length T ys)

def replaceXImplicit {T : Type} (point : PPoint T) (newX : T) : PPoint T :=
  { point with x := newX }

#eval replaceXImplicit natOrigin 5 -- 5,0

def lengthImplicit {T : Type} (xs : List T) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (lengthImplicit ys)

#eval lengthImplicit primesUnder10

inductive MyOption (T : Type) : Type where
  | none           : MyOption T
  | some (val : T) : MyOption T

def List.myhead? {T : Type} (xs : List T) : Option T :=
  match xs with
  | []     => none
  | y :: _ => some y

#eval [1, 2, 3].myhead? -- some 1
#eval ([] : List Int).myhead? -- none
#eval primesUnder10.head? -- some 2

structure MyProd (T : Type) (S : Type) : Type where
  fst : T
  snd : S

def fives : Prod String Int := ("five", 5)
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)

inductive MySum (T : Type) (S : Type) : Type where
  | inl : T → MySum T S
  | inr : S → MySum T S

def PetName : Type := String ⊕ String
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | []                    => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

inductive MyUnit : Type where
  | unit : MyUnit

inductive ArithExpr (ann : Type) : Type where
  | int   : ann → Int           → ArithExpr ann
  | plus  : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

-- breaking the type system
-- inductive MyType : Type where
--   | ctor : (T : Type) → T → MyType

-- inductive MyType : Type where
--   | ctor : (MyType → Int) → MyType

-- inductive MyType (T : Type) : Type where
--   | ctor : T → MyType

inductive MyType (T : Type) : Type where
  | ctor : T → MyType T

-- def ofFive : MyType := ctor 5
def ofFive : MyType Nat := MyType.ctor 5

-- Write a function to find the last entry in a list. It should return an Option.
def List.findLast {T : Type} (xs : List T) : Option T :=
  match xs with
  | []      => none
  | [y]     => some y
  | _ :: ys => findLast ys

#eval ([] : List Nat).findLast -- none
#eval [1, 2, 3].findLast       -- some 3

-- Write a function that finds the first entry in a list that satisfies a given predicate.
-- Start the definition with
-- def List.findFirst? {T : Type} (xs : List T) (predicate : T → Bool) : Option T :=
def List.findFirst? {T : Type} (xs : List T) (p : T -> Bool) : Option T :=
  match xs with
  | []      => none
  | y :: ys => if p y then some y else findFirst? ys p

def p (t : Nat) : Bool := t % 2 = 0
#eval [1, 2, 3].findFirst? (. % 2 = 0) -- some 2
#eval [1, 3, 3].findFirst? p -- none

-- Write a function Prod.swap that swaps the two fields in a pair.
-- Start the definition with
-- def Prod.swap {T S : Type} (pair : T × S) : S × T :=
def Prod.swap {T S : Type} (pair : T × S) : S × T := (pair.snd, pair.fst)
#eval (1, 2).swap -- (2, 1)

-- Rewrite the PetName example to use a custom datatype and
-- compare it to the version that uses Sum.
inductive MyPet where
  | fst (name : String) : MyPet
  | snd (name : String) : MyPet

def myAnimals : List MyPet :=
  [MyPet.fst "Spot", MyPet.snd "Tiger", MyPet.fst "Fifi", MyPet.fst "Rex", MyPet.snd "Floof"]

def howManyPets (pets : List MyPet) : Nat :=
  match pets with
  | [] => 0
  | MyPet.fst _ :: morePets => howManyPets morePets + 1
  | MyPet.snd _ :: morePets => howManyPets morePets

-- Write a function zip that combines two lists into a list of pairs.
-- The resulting list should be as long as the shortest input list.
-- Start the definition with
-- def zip {T S : Type} (xs : List T) (ys : List S) : List (T × S) :=.
def zip {T S : Type} (xs : List T) (ys : List S) : List (T × S) :=
  match xs with
  | []       => []
  | x :: xs' =>
    match ys with
    | []       => []
    | y :: ys' => (x, y) :: zip xs' ys'

#eval zip [1, 2, 3] [4, 5, 6] -- 14 25 36
#eval zip [1, 2] [4, 5, 6] -- 14 25
#eval zip [1, 2, 3] [4, 5] -- 14 25

-- Write a polymorphic function take that returns the first n
-- entries in a list, where n is a Nat.
-- If the list contains fewer than n entries, then the resulting list should be
-- the input list.
-- #eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"], and
-- #eval take 1 ["bolete", "oyster"] should yield ["bolete"].
def take {T : Type} (n : Nat) (xs : List T) : List T :=
  match n with
  | Nat.zero   => []
  | Nat.succ m =>
    match xs with
    | []       => []
    | x :: xs' => x :: take m xs'
#eval take 3 ["bolete", "oyster"] -- ["bolete", "oyster"]
#eval take 1 ["bolete", "oyster"] -- ["bolete" ]

-- Using the analogy between types and arithmetic,
-- write a function that distributes products over sums.
-- In other words, it should have type T × (S ⊕ γ) → (T × S) ⊕ (T × γ).
def dist {T S U : Type} (input : T × (S ⊕ U)) : (T × S) ⊕ (T × U) :=
  match input.snd with
  | Sum.inl s => Sum.inl (input.fst, s)
  | Sum.inr u => Sum.inr (input.fst, u)

-- Using the analogy between types and arithmetic,
-- write a function that turns multiplication by two into a sum.
-- In other words, it should have type Bool × T → T ⊕ T.
def double {T : Type} (input : Bool × T) : T ⊕ T :=
  match input.fst with
  | true  => Sum.inl input.snd
  | false => Sum.inr input.snd
