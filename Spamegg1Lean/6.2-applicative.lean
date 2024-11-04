instance : Applicative Option where
  pure    := .some
  seq f x := -- f : Option (α -> β) and x : Unit -> Option α
    match f with
    | none   => none
    | some g => (x ()).map g

instance : Applicative (Except ε) where
  pure    := .ok
  seq f x := -- f : Except (α -> β)
    match f with
    | .error e => .error e
    | .ok g    => (x ()).map g

-- counterexample: functor that is not applicative
structure Pair (α β : Type) : Type where
  first  : α
  second : β

instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩

-- need pure for Applicative (Pair α)
-- def Pair.pure (x : β) : Pair α β := Pair.mk _ x -- there is no α value!

structure RawInput where
  name      : String
  birthYear : String

-- Lean built-in
namespace Subtyping
structure Subtype {α : Type} (p : α → Prop) where
  val      : α
  property : p val
end Subtyping

def FastPos : Type := {x : Nat // x > 0} -- subtype of Nat
def one : FastPos := ⟨1, by simp⟩ -- 2nd arg is proof that it's > 0

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp_arith⟩
def two : FastPos := 2 -- now we don't need the proof, thanks to OfNat

def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then some ⟨n, h⟩ else none

-- validating input
structure CheckedInput (thisYear : Nat) : Type where
  name      : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
deriving Repr

-- from before
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

def hAppendNel : (NonEmptyList α) -> (NonEmptyList α) -> (NonEmptyList α)
| {head := x, tail := xs}, {head := y, tail := ys} =>
  {head := x, tail := xs ++ (y :: ys)}

instance : HAppend (NonEmptyList α) (NonEmptyList α) (NonEmptyList α) where
  hAppend := hAppendNel

-- new
inductive Validate (ε α : Type) : Type where
  | ok     : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
  | .ok x        => .ok (f x)
  | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure    := .ok
  seq f x :=
    match f with
    | .ok g        => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _         => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Field := String
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then reportError "name" "Required"
  else pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x        => next x

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none   => reportError "birth year" "Must be digits"
  | some n => pure n

def checkBirthYear (thisYear year : Nat) : Validate (Field × String)
  {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

def checkInput (year : Nat) (input : RawInput)
  : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat

#eval checkInput 2023 {name := "David", birthYear := "1984"}
#eval checkInput 2023 {name := "", birthYear := "2045"}
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}

def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }

def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }
