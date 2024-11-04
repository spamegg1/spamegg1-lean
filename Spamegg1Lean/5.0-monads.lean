namespace MonadList

def first (xs : List α) : Option α :=
  xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none       => none
  | some first =>
    match xs[2]? with
    | none       => none
    | some third => some (first, third)

def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none       => none
  | some first =>
    match xs[2]? with
    | none       => none
    | some third =>
      match xs[4]? with
      | none       => none
      | some fifth => some (first, third, fifth)

def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none       => none
  | some first =>
    match xs[2]? with
    | none       => none
    | some third =>
      match xs[4]? with
      | none       => none
      | some fifth =>
        match xs[6]? with
        | none         => none
        | some seventh => some (first, third, fifth, seventh)

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none   => none
  | some x => next x

def firstThirdBetter (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third => some (first, third)

def firstThirdBest (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
  andThen xs[2]? (fun third =>
  some (first, third)))

infixl:55 " ~~> " => andThen

def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)

def firstThirdFifthSeventhBetter (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)
end MonadList

namespace MonadExcept
-- built-in Lean exception datatype
-- inductive Except (ε : Type) (α : Type) where
--   | error : ε → Except ε α
--   | ok    : α → Except ε α
-- deriving BEq, Hashable, Repr

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none   => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]

#eval get ediblePlants 2 -- ok
#eval get ediblePlants 4 -- error

-- built-in List method
-- def first (xs : List α) : Except String α :=
--   get xs 0

def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first  =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third  =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth  =>
        match get xs 6 with
        | Except.error msg  => Except.error msg
        | Except.ok seventh => Except.ok (first, third, fifth, seventh)

def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x      => next x

def firstThird (xs : List α) : Except String (α × α) :=
  andThen (get xs 0) fun first =>
  andThen (get xs 2) fun third =>
  Except.ok (first, third)

def ok (x : α) : Except ε α := Except.ok x
def fail (err : ε) : Except ε α := Except.error err

def get2 (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none   => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x

infixl:55 " ~~> " => andThen

def firstThirdBetter (xs : List α) : Except String (α × α) :=
  get2 xs 0 ~~> fun first =>
  get2 xs 2 ~~> fun third =>
  ok (first, third)

def firstThirdFifthSeventhBetter (xs : List α) : Except String (α × α × α × α) :=
  get2 xs 0 ~~> fun first   =>
  get2 xs 2 ~~> fun third   =>
  get2 xs 4 ~~> fun fifth   =>
  get2 xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)
end MonadExcept

-- from before
inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

namespace MonadLog
-- Logging
def isEven (i : Int) : Bool := i % 2 == 0

def sumAndFindEvens : List Int → List Int × Int
  | []      => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    (if isEven i then i :: moreEven else moreEven, sum + i)

def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf         => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum)   := inorderSum l
    let (hereVisited, hereSum)   := ([x], x)
    let (rightVisited, rightSum) := inorderSum r
    (leftVisited ++ hereVisited ++ rightVisited, leftSum + hereSum + rightSum)

def sumAndFindEvens2 : List Int → List Int × Int
  | []      => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens2 is
    let (evenHere, ())  := (if isEven i then [i] else [], ())
    (evenHere ++ moreEven, sum + i)

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok (x : β) : WithLog α β := {log := [], val := x}
def save (data : α) : WithLog α Unit := {log := [data], val := ()}

def sumAndFindEvensBetter : List Int → WithLog Int Int
  | []      => ok 0
  | i :: is =>
    andThen (if isEven i then save i else ok ()) fun () =>
    andThen (sumAndFindEvensBetter is) fun sum =>
    ok (i + sum)

def inorderSumBetter : BinTree Int → WithLog Int Int
  | BinTree.leaf         => ok 0
  | BinTree.branch l x r =>
    andThen (inorderSumBetter l) fun leftSum =>
    andThen (save x) fun () =>
    andThen (inorderSumBetter r) fun rightSum =>
    ok (leftSum + x + rightSum)

infixl:55 " ~~> " => andThen

def sumAndFindEvensBest : List Int → WithLog Int Int
  | []      => ok 0
  | i :: is =>
    (if isEven i then save i else ok ()) ~~> fun () =>
    sumAndFindEvensBest is ~~> fun sum =>
    ok (i + sum)

def inorderSumBest : BinTree Int → WithLog Int Int
  | BinTree.leaf         => ok 0
  | BinTree.branch l x r =>
    inorderSumBest l ~~> fun leftSum =>
    save x ~~> fun () =>
    inorderSumBest r ~~> fun rightSum =>
    ok (leftSum + x + rightSum)
end MonadLog

-- numbering tree nodes
namespace MonadTreeNodes
open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf                => (n, BinTree.leaf)
    | BinTree.branch left x right =>
      let (k, numberedLeft)  := helper n left
      let (i, numberedRight) := helper (k + 1) right
      (i, BinTree.branch numberedLeft (k, x) numberedRight)
  (helper 0 t).snd

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

infixl:55 " ~~> " => andThen

def numberBetter (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf                => ok BinTree.leaf
    | BinTree.branch left x right =>
      helper left  ~~> fun numberedLeft =>
      get          ~~> fun n =>
      set (n + 1)  ~~> fun () =>
      helper right ~~> fun numberedRight =>
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

end MonadTreeNodes
