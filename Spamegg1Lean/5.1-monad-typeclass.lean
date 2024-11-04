-- Monad typeclass built-in to Lean
-- class Monad (m : Type → Type) where
--   pure :   α → m α             -- this is UNIT
--   bind : m α → (α → m β) → m β -- this is FLATMAP >>=

-- instance : Monad Option where
--   pure          := some
--   bind opt next :=
--     match opt with
--     | none   => none
--     | some x => next x

instance : Monad (Except ε) where
  pure              := Except.ok
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x    => next x

def firstThirdFifthSeventh [Monad m]
  (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals -- none
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds   -- some ...

def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none   => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

#eval firstThirdFifthSeventh getOrExcept slowMammals

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | []      => pure []
  | x :: xs =>
    f x       >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)

-- from before
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def ok (x : α) : State σ α :=
  fun s => (s, x)

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

-- new
instance : Monad (State σ) where
  pure x          := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def increment (howMuch : Int) : State Int Int :=
  get               >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i

#eval mapM increment [1, 2, 3, 4, 5] 0 -- 15, 0 1 3 6 10: sum with seq. of partial sums

-- from before
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
deriving Repr

def save (data : α) : WithLog α Unit := {log := [data], val := ()}

def isEven (i : Int) : Bool := i % 2 == 0

-- new
instance : Monad (WithLog logged) where
  pure x           := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}

def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then save i else pure ()) >>= fun () =>
  pure i

#eval mapM saveIfEven [1, 2, 3, 4, 5] -- log [2, 4]

-- Identity monad
-- def Id (t : Type) : Type := t
instance : Monad Id where
  pure x   := x
  bind x f := f x

#eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5] -- needs the m = id type hint!

-- monad laws
-- 1. pure (unit) is a left  identity of bind (flatMap)
-- 2. pure (unit) is a right identity of bind (flatMap)
-- 3. bind is associative
-- 1. bind (pure v) f = f v, in other words: (unit v).flatMap(f) = f v
-- 2. bind v pure = v,       in other words: v.flatMap(unit) = v
-- 3. bind (bind v f) g = bind v (fun x => bind (f x) g)
-- 3. in other words: v.flatMap(f).flatMap(g) = v.flatMap(x => f(x).flatMap(g))

-- Exercises
-- Mapping on a Tree
inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr
-- Define a function BinTree.mapM.
-- By analogy to mapM for lists, this function should apply a monadic function
-- to each data entry in a tree, as a preorder traversal. The type signature should be:
def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
| BinTree.leaf         => pure BinTree.leaf
| BinTree.branch l a r =>
  bind (f a)              fun b  =>
  bind (BinTree.mapM f l) fun lb =>
  bind (BinTree.mapM f r) fun rb =>
  pure (BinTree.branch lb b rb)

-- The Option Monad Contract
-- First, write a convincing argument that the Monad instance for Option
-- satisfies the monad contract. Then, consider the following instance:
instance : Monad Option where
  pure x        := some x
  bind opt next := none
-- Both methods have the correct type.
-- Why does this instance violate the monad contract?

-- Answer: left identity fails:
def v := some 3
#eval bind (pure v) id -- none
#eval id v             -- some 3

-- right identity fails:
#eval bind v pure -- none
#eval v           -- some 3

-- associativity is OK (I think?)
#eval bind (bind v some) some              -- none
#eval bind v (fun x => bind (some x) some) -- none
