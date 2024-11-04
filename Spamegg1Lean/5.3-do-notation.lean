def firstThirdFifthSeventhOld [Monad m]
  (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def firstThirdFifthSeventh [Monad m]
  (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
  let first   ← lookup xs 0
  let third   ← lookup xs 2
  let fifth   ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)

-- from before
inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def ok (x : α) : State σ α :=
  fun s => (s, x)

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

instance : Monad (State σ) where
  pure x          := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => andThen
-- end of from before

-- old
def numberOld (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf         => ok BinTree.leaf
    | BinTree.branch l x r =>
      helper l    ~~> fun numberedLeft  =>
      get         ~~> fun n             =>
      set (n + 1) ~~> fun ()            =>
      helper r    ~~> fun numberedRight =>
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

-- new, rewritten with do notation
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf                => pure BinTree.leaf
    | BinTree.branch left x right => do
      let numberedLeft ← helper left
      let n ← get
      set (n + 1)
      let numberedRight ← helper right
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

-- old
def mapMold [Monad m] (f : α → m β) : List α → m (List β)
  | []      => pure []
  | x :: xs =>
    f x          >>= fun hd =>
    mapMold f xs >>= fun tl =>
    pure (hd :: tl)

-- new
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | []      => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM f xs
    pure (hd :: tl)

def mapM2 [Monad m] (f : α → m β) : List α → m (List β)
  | []      => pure []
  | x :: xs => do pure ((← f x) :: (← mapM2 f xs))

def increment : State Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

def number2 (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf         => pure BinTree.leaf
    | BinTree.branch l x r => do
      pure (BinTree.branch (← helper l) ((← increment), x) (← helper r))
  (helper t 0).snd

-- Rewrite evaluateM, its helpers, and the different specific
-- use cases using do-notation instead of explicit calls to >>=.
inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

-- old
def evaluateMold [Monad m] (applyPrim : Arith → Int → Int → m Int): Expr Arith → m Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 =>
    evaluateMold applyPrim e1 >>= fun v1 =>
    evaluateMold applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2

-- new
def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int): Expr Arith → m Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 => do
    applyPrim p (<- evaluateM applyPrim e1) (<- evaluateM applyPrim e2)

-- Rewrite firstThirdFifthSeventh using nested actions.
def firstThirdFifthSeventh2 [Monad m]
  (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
  pure ((← lookup xs 0), (← lookup xs 2), (← lookup xs 4), (← lookup xs 6))
