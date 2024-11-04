inductive Vect (α : Type u) : Nat → Type u where
  | nil  : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
deriving Repr

-- example : Vect String 3 := Vect.nil -- type mismatch
-- example : Vect String n := Vect.nil -- type mismatch
-- example : Vect String n := Vect.cons "Hello" (Vect.cons "world" Vect.nil)

-- When pattern matching refines the type of a program in addition to discovering the
-- structure of a value, it is called dependent pattern matching.
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0     => .nil
  | k + 1 => .cons x (replicate k x)

-- wrong length, but type-checks.
-- def List.replicate (n : Nat) (x : α) : List α :=
--   match n with
--   | 0     => []
--   | k + 1 => x :: x :: replicate k x

-- wrong length is caught by type error:
-- def Vect.replicate (n : Nat) (x : α) : Vect α n :=
--   match n with
--   | 0     => .nil
--   | k + 1 => .cons x (.cons x (replicate k x)) -- type error

#eval ["Mount Hood", "Mount Jefferson", "South Sister"].zip
  ["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]

#eval [3428.8, 3201, 3158.5, 3075, 3064].zip [170.86, 170.77, 170.35] -- ignore extras
-- F# instead throws error when lists have different lengths.

-- without vector, we get missing cases error
-- def zip : List α → List β → List (α × β)
--   | [], [] => [] -- missing cases!
--   | x :: xs, y :: ys => (x, y) :: zip xs ys

-- require both lists to have same length. Cases are not exhaustive but it's OK.
-- .nil and .cons REFINE the types, so type checker has length info.
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil             => .nil
  -- | .nil, .cons y ys       => .nil -- type error, lengths are unequal
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

-- make length into an explicit argument to see this:
def Vect.zip2 : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
  | 0, .nil, .nil                 => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip2 k xs ys)

-- Double-check that Vect.zip gives the right answer when combining the three highest
-- peaks in Oregon with the three highest peaks in Denmark.
-- Because Vect doesn't have the syntactic sugar that List has,
-- it can be helpful to begin by defining oregonianPeaks : Vect String 3 and
-- danishPeaks : Vect String 3.
def oregonianPeaks : Vect String 3 :=
  Vect.cons "Mount Hood" (Vect.cons "Mount Jefferson" (Vect.cons "South Sister" Vect.nil))
def danishPeaks : Vect String 3 :=
  Vect.cons "Møllehøj" (Vect.cons "Yding Skovhøj" (Vect.cons "Ejer Bavnehøj" Vect.nil))
#eval oregonianPeaks.zip danishPeaks

-- Define a function Vect.map with type (α → β) → Vect α n → Vect β n.
def Vect.map : (α → β) → Vect α n → Vect β n
| f, .nil       => .nil
| f, .cons x xs => .cons (f x) (Vect.map f xs)
#eval (Vect.cons 1 (Vect.cons 2 Vect.nil)).map (. + 2) -- 3, 4

-- Define a function Vect.zipWith that combines the entries in a Vect one at a time
-- with a function.
-- It should have the type (α → β → γ) → Vect α n → Vect β n → Vect γ n.
def Vect.zipWith : (α → β → γ) → Vect α n → Vect β n → Vect γ n
| _, .nil, _                => .nil
| f, .cons x xs, .cons y ys => .cons (f x y) (Vect.zipWith f xs ys)

#eval Vect.zipWith (. ++ "&&" ++ .) oregonianPeaks danishPeaks

-- Define a function Vect.unzip that splits a Vect of pairs into a pair of Vects.
-- It should have the type Vect (α × β) n → Vect α n × Vect β n.
def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
| .nil             => (.nil, .nil)
| .cons (x, y) xys =>
  let (xs, ys) := Vect.unzip xys
  (.cons x xs, .cons y ys)

def zipped := Vect.zip oregonianPeaks danishPeaks
#eval Vect.unzip zipped

-- Define a function Vect.snoc that adds an entry to the end of a Vect.
-- Its type should be Vect α n → α → Vect α (n + 1) and
-- #eval Vect.snoc (.cons "snowy" .nil) "peaks"
-- should yield Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil)).
-- The name snoc is a traditional functional programming pun: it is cons backwards.
def Vect.snoc : Vect α n → α → Vect α (n + 1)
| .nil, y       => .cons y .nil
| .cons x xs, y => .cons x (Vect.snoc xs y)

#eval Vect.snoc (.cons "snowy" .nil) "peaks" -- .cons "snowy" (.cons "peaks" .nil)

-- Define a function Vect.reverse that reverses the order of a Vect.
def Vect.reverse : Vect α n → Vect α n
| .nil       => .nil
| .cons x xs => .snoc (Vect.reverse xs) x

#eval Vect.reverse (.cons "snowy" (.cons "peaks" .nil)) -- peaks snowy

-- Define a function Vect.drop with the following type:
-- (n : Nat) → Vect α (k + n) → Vect α k.
-- Verify that it works by checking that
-- #eval danishPeaks.drop 2
-- yields Vect.cons "Ejer Bavnehøj" (Vect.nil).
def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
| 0, v              => v
| m + 1, .cons _ xs => Vect.drop m xs

#eval danishPeaks.drop 2 -- Vect.cons "Ejer Bavnehøj" (Vect.nil).

-- Define a function Vect.take with type
-- (n : Nat) → Vect α (k + n) → Vect α n
-- that returns the first n entries in the Vect. Check that it works on an example.
def Vect.take : (n : Nat) -> Vect α (k + n) -> Vect α n
| 0, _              => .nil
| m + 1, .cons x xs => .cons x (Vect.take m xs)

#eval danishPeaks.take 1 -- Vect.cons "Møllehøj" (Vect.nil)
