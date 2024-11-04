-- omitting implicit type parameters
def length (xs : List T) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (length ys)

#eval length [1, 2, 3]

-- omitting the input parameter and the match clause
def length2 : List T -> Nat
  | []      => 0
  | _ :: ys => Nat.succ (length ys)

#eval length2 [1, 2, 3]

def drop : Nat → List α → List α
  | Nat.zero, xs        => xs
  | _, []               => []
  | Nat.succ n, _ :: xs => drop n xs

def fromOption (default : α) : Option α → α
  | none => default
  | some x => x

#eval (some "salmonberry").getD ""

def unzipSlow : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    (x :: (unzipSlow xys).fst, y :: (unzipSlow xys).snd)

def unzipEff : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) := unzipEff xys
    (x :: xs, y :: ys)

#eval unzipEff [(1, 4), (2, 5), (3, 6)]

def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

#eval reverse [1, 2, 3]

-- omitting return type, thanks to the match expression
def unzip (pairs : List (α × β)) :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)

def drop2 (n : Nat) (xs : List α) : List α :=
  match n, xs with -- simultaneous matching
  | Nat.zero, ys         => ys
  | _, []                => []
  | Nat.succ n , _ :: ys => drop2 n ys

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ k => not (even k)

-- natural number specific patterns
def even2 : Nat → Bool
  | 0     => true
  | n + 1 => not (even2 n)

def halve : Nat → Nat
  | 0     => 0
  | 1     => 0
  | n + 2 => halve n + 1

-- anonymous functions
#check fun x => x + 1         -- Nat -> Nat
#check fun (x : Int) => x + 1 -- Int -> Int
#check λ {α : Type} (x : α) => x -- fun {α} x => x : {α : Type} → α → α

#check fun
  | 0     => none
  | n + 1 => some n

#eval (· * 2) 5

def Nat.double : Nat → Nat := fun
  | 0     => 0
  | k + 1 => double k + 2

#eval (4 : Nat).double

namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace

#check NewNamespace.triple

def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)

inductive Elt : Type where
  | lineBreak
  | string : String → Elt
  | emph   : Elt → Elt
  | strong : Elt → Elt

def Elt.string? (elt : Elt) : Option String :=
  match elt with
  | Elt.string s => some s
  | _            => none

def Elt.string2? (elt : Elt) : Option String :=
  if let Elt.string s := elt then some s else none

#eval s!"three fives is {NewNamespace.triple 5}"
