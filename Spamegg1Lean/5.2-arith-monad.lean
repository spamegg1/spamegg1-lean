inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Arith where
  | plus
  | minus
  | times
  | div

open Expr in
open Arith in
def twoPlusThree : Expr Arith := prim plus (const 2) (const 3)

open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))

-- option
def applyPrimOption : Arith → Int → Int → Option Int
  | Arith.plus, x, y  => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y   => if y == 0 then none else pure (x / y)

def evaluateOption : Expr Arith → Option Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    applyPrimOption p v1 v2

#eval evaluateOption fourteenDivided -- none

-- exception
def applyPrimExcept : Arith → Int → Int → Except String Int
  | Arith.plus, x, y  => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y   =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateExcept : Expr Arith → Except String Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 =>
    evaluateExcept e1 >>= fun v1 =>
    evaluateExcept e2 >>= fun v2 =>
    applyPrimExcept p v1 v2

-- polymorphic, works for both option and exception
def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int): Expr Arith → m Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2

#eval evaluateM applyPrimOption fourteenDivided -- none
#eval evaluateM applyPrimExcept fourteenDivided -- exception

-- refactor
def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then none else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | Arith.plus, x, y  => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y   => applyDiv x y

def evaluateM2 [Monad m] (applyDiv : Int → Int → m Int): Expr Arith → m Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 =>
    evaluateM2 applyDiv e1 >>= fun v1 =>
    evaluateM2 applyDiv e2 >>= fun v2 =>
    applyPrim applyDiv p v1 v2

-- other effects, more general
namespace MoreGeneralEffects

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m]
  (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y     => pure (x + y)
  | Prim.minus, x, y    => pure (x - y)
  | Prim.times, x, y    => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m]
  (applySpecial : special → Int → Int → m Int): Expr (Prim special) → m Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2


-- no effects, can be used in any monad
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int := nomatch op

open Expr Prim in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14))) -- -9

-- nondeterministic arithmetic
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

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | []      => if goal == 0 then pure [] else Many.none
  | x :: xs =>
    if x > goal then addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
          pure (x :: answer))

inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y => Many.fromList [x, y]
  | NeedsSearch.div, x, y    => if y == 0 then Many.none else Many.one (x / y)

open Expr Prim NeedsSearch
#eval (evaluateM applySearch (prim plus (const 1) (prim (other choose) (const 2) (const 5)))).takeAll
#eval (evaluateM applySearch (prim plus (const 1) (prim (other div) (const 2) (const 0)))).takeAll
#eval (evaluateM applySearch (prim (other div) (const 90) (prim plus (prim (other choose) (const (-5)) (const 5)) (const 5)))).takeAll

-- custom environments, reader monads
def Reader (ρ : Type) (α : Type) : Type := ρ → α
def read : Reader ρ ρ := fun env => env
def Reader.pure (x : α) : Reader ρ α := fun _ => x

def Reader.bind (result : Reader ρ α) (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env

instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env

abbrev Env : Type := List (String × (Int → Int → Int))
def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)

open Expr Prim in
#eval evaluateM applyPrimReader (prim (other "max") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv

-- Checking Contracts
-- Check the monad contract for State σ and Except ε.

-- Readers with Failure
-- Adapt the reader monad example so that it can also indicate failure
-- when the custom operator is not defined, rather than just returning zero.
-- In other words, given these definitions:
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α
def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α

-- do the following:
-- 1. Write suitable pure and bind functions
-- 2. Check that these functions satisfy the Monad contract
-- 3. Write Monad instances for ReaderOption and ReaderExcept
-- 4. Define suitable applyPrim operators and
-- test them with evaluateM on some example expressions

-- A Tracing Evaluator
-- The WithLog type can be used with the evaluator to add optional tracing of some ops.
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
deriving Repr

-- In particular, the type ToTrace can serve as a signal to trace a given operator:
inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α

-- For the tracing evaluator, expressions should have type
-- Expr (Prim (ToTrace (Prim Empty))).
-- This says that the operators in the expression consist of
-- addition, subtraction, and multiplication, augmented with traced versions of each.
-- The innermost argument is Empty to signal that there are no further
-- special operators inside of trace, only the three basic ones.

-- Do the following:
-- Implement a Monad (WithLog logged) instance
-- Write an applyTraced function to apply traced operators to their arguments,
-- logging both the operator and the arguments, with type
-- ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int

-- If the exercise has been completed correctly, then should result in:
-- open Expr Prim ToTrace in
-- #eval evaluateM applyTraced (prim (other (trace times)) (prim (other (trace plus)) (const 1) (const 2)) (prim (other (trace minus)) (const 3) (const 4)))
-- { log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }

-- Hint: values of type Prim Empty will appear in the resulting log.
-- In order to display them as a result of #eval, the following instances are required:
deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim

end MoreGeneralEffects
