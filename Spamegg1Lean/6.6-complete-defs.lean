-- actual universe polymorphic definitions in Lean
class MyFunctor (f : Type u → Type v) : Type (max (u+1) v) where
  map      : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α :=
    Function.comp map (Function.const _)

def simpleConst  (x : α) (_ : β) : α := x -- ignore 2nd arg
#eval [1, 2, 3].map (simpleConst "same") -- same same same

-- showing why max (u+1) v is correct:
class Functor1 (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β

-- equivalent to:
inductive Functor2 (f : Type u → Type v) : Type (max (u+1) v) where
  | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor2 f

-- App: start with Pure and Seq
class MyPure (f : Type u → Type v) : Type (max (u+1) v) where
  pure {α : Type u} : α → f α

class MySeq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

class MySeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β

class MySeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α

class MyApplicative (f : Type u → Type v)
extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b

-- monad
class MyBind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β

class MyMonad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()


-- Understand the default implementations of map, seq, seqLeft, and seqRight in Monad
-- by working through examples such as Option and Except.
-- In other words, substitute their definitions for bind and pure
-- into the default definitions, and simplify them to recover the versions
-- map, seq, seqLeft, and seqRight that would be written by hand.

-- On paper or in a text file, prove to yourself that the default implementations of
-- map and seq satisfy the contracts for Functor and Applicative.
-- In this argument, you're allowed to use the rules from the Monad contract
-- as well as ordinary expression evaluation.
