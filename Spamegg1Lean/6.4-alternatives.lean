abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) → String → LegacyCheckedInput
  | humanAfter1970  :
    (birthYear : {y : Nat // y > 1970}) → NonEmptyString → LegacyCheckedInput
  | company         : NonEmptyString → LegacyCheckedInput
deriving Repr

-- from before
structure RawInput where
  name      : String
  birthYear : String

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

inductive Validate (ε α : Type) : Type where
  | ok     : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

def hAppendNel : (NonEmptyList α) -> (NonEmptyList α) -> (NonEmptyList α)
| {head := x, tail := xs}, {head := y, tail := ys} =>
  {head := x, tail := xs ++ (y :: ys)}

instance : HAppend (NonEmptyList α) (NonEmptyList α) (NonEmptyList α) where
  hAppend := hAppendNel

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

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none   => reportError "birth year" "Must be digits"
  | some n => pure n

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x        => next x

-- new
def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x         => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x         => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

-- Lean built-in
-- class OrElse (α : Type) where
--   orElse : α → (Unit → α) → α

instance : OrElse (Validate ε α) where
  orElse := Validate.orElse

def checkThat (condition : Bool) (field : Field) (msg : String)
  : Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg

def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" <*>
    checkName input.name

-- Lean built-in
-- class SeqRight (f : Type → Type) where
--   seqRight : f α → (Unit → f β) → f β

def checkCompany2 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  pure .company <*> checkName input.name

def checkCompany3 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  .company <$> checkName input.name

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε)
  : Validate ε {x : α // p x} :=
  if h : p v then pure ⟨v, h⟩ else .errors { head := err, tail := [] }

def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970) ("birth year", "less than 1970") <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) ("birth year", "greater than 1970") <*>
      checkName input.name

def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩ -- ok
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
#eval checkLegacyInput ⟨"", "1963"⟩ -- ok
#eval checkLegacyInput ⟨"", "1970"⟩ -- 5 errors

-- Lean built-in
-- class Alternative (f : Type → Type) extends Applicative f where
--   failure : f α
--   orElse : f α → (Unit → f α) → f α

instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse

instance : Alternative Option where
  failure := none
  orElse
    | some x, _ => some x
    | none, y   => y ()

-- from before
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys      => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.fromList : List α → Many α
  | []      => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _                  => []
  | _ + 1, Many.none      => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none      => []
  | Many.more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _      => Many.none
  | Many.more x xs, f => (f x).union (bind (xs ()) f)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

-- new
def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys      => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

instance : Alternative Many where
  failure := .none
  orElse  := Many.orElse

-- Lean built-in
-- def guard [Alternative f] (p : Prop) [Decidable p] : f Unit :=
--   if p then pure () else failure

def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k

#eval (evenDivisors 20).takeAll -- 20 10 4 2

-- Improve Validation Friendliness
-- The errors returned from Validate programs that use <|> can be difficult to read,
-- because inclusion in the list of errors simply means that the error can be reached
-- through some code path. A more structured error report can be used to guide the
-- user through the process more accurately:

-- Replace the NonEmptyList in Validate.error with a bare type variable,
-- and then update the definitions of the Applicative (Validate ε) and
-- OrElse (Validate ε α) instances to require only that there be an
-- Append ε instance available.

-- Define a function
def Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α := sorry
-- that transforms all the errors in a validation run.

-- Using the datatype TreeError to represent errors, rewrite the legacy validation
-- system to track its path through the three alternatives.

-- Write a function report : TreeError → String that outputs a user-friendly
-- view of the TreeError's accumulated warnings and errors.
inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both
