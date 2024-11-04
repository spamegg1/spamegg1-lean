inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

-- def seven : Pos := 7 -- numerals are polymorphic
def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

-- def fourteen : Pos := seven + seven -- nope
-- def fortyNine : Pos := seven * seven -- nope

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

open Plus (plus)

#eval plus 5 3

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k    => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

-- def posToString (atTop : Bool) (p : Pos) : String :=
--   let paren s := if atTop then s else "(" ++ s ++ ")"
--   match p with
--   | Pos.one => "Pos.one"
--   | Pos.succ n => paren s!"Pos.succ {posToString false n}"

-- instance : ToString Pos where
--   toString := posToString true

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

def fourteen : Pos := plus seven seven
#eval fourteen

instance : Add Pos where
  add := Pos.plus

def fourteen2 : Pos := seven + seven
#eval fourteen2

#eval s!"There are {seven}"

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

#eval [seven * Pos.one, seven * seven, Pos.succ Pos.one * seven]

inductive LT4 where
  | zero
  | one
  | two
  | three
deriving Repr

instance : OfNat LT4 0 where
  ofNat := LT4.zero
instance : OfNat LT4 1 where
  ofNat := LT4.one
instance : OfNat LT4 2 where
  ofNat := LT4.two
instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4) -- LT4.three
-- #eval (4 : LT4) -- not allowed

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0     => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def eight : Pos := 8
-- def zero : Pos := 0 -- not allowed in Pos

-- Another Representation
-- An alternative way to represent a positive number is as the successor of some Nat.
-- Replace the definition of Pos with a structure
-- whose constructor is named succ that contains a Nat:
structure Pos2 where
  succ ::
  pred : Nat

-- Define instances of Add, Mul, ToString, and OfNat
-- that allow this version of Pos to be used conveniently.
def Pos2.plus : Pos2 → Pos2 → Pos2
  | Pos2.succ n, Pos2.succ m  => Pos2.succ (n + m + 1)

def Pos2.mul : Pos2 → Pos2 → Pos2
  | Pos2.succ n, Pos2.succ m  => Pos2.succ (n * m + n + m)

def Pos2.toNat : Pos2 → Nat
  | Pos2.succ n => n + 1

instance : Add Pos2 where
  add := Pos2.plus
instance : Mul Pos2 where
  mul := Pos2.mul
instance : ToString Pos2 where
  toString x := toString (x.toNat)
instance : OfNat Pos2 (n + 1) where
  ofNat := Pos2.succ n

#eval (3 : Pos2) * (4 : Pos2) -- 12
#eval (10 : Pos2) + (2 : Pos2) -- 12
-- #eval (0 : Pos2) -- not allowed

-- Even Numbers
-- Define a datatype that represents only even numbers.
-- Define instances of Add, Mul, and ToString that allow it to be used conveniently.
-- OfNat requires a feature that is introduced in the next section.
inductive Even where
  | zero : Even
  | succ : Even -> Even

def Even.toNat : Even → Nat
  | Even.zero   => 0
  | Even.succ e => e.toNat + 2

def Even.add : Even -> Even -> Even
  | Even.zero, e     => e
  | Even.succ e1, e2 => Even.succ (Even.add e1 e2)

def Even.dbl : Even -> Even
  | Even.zero   => Even.zero
  | Even.succ e => Even.succ (Even.succ (Even.dbl e))

def Even.mul : Even -> Even -> Even
  | Even.zero, _     => Even.zero
  | Even.succ e1, e2 => Even.add (Even.mul e1 e2) (Even.dbl e2)

instance : ToString Even where
  toString x := toString (x.toNat)

instance : Add Even where
  add := Even.add

instance : Mul Even where
  mul := Even.mul

def zero := Even.zero
def two := Even.succ zero
def four := Even.succ two
#eval zero -- 0
#eval two -- 2
#eval four -- 4
#eval two.dbl -- 4
#eval four.dbl -- 8
#eval two + four -- 6
#eval four + two -- 6
#eval two * four -- 8
#eval four * two -- 8
#eval four * four -- 16
#eval (four * four).dbl.dbl + (two + four) * four * two + four * zero -- 64 + 48 + 0 = 112

-- HTTP Requests
-- An HTTP request begins with an identification of a HTTP method, such as GET or POST,
-- along with a URI and an HTTP version.
-- Define an inductive type that represents an interesting subset of the HTTP methods,
-- and a structure that represents HTTP responses.
-- Responses should have a ToString instance that makes it possible to debug them.
-- Use a type class to associate different IO actions with each HTTP method,
-- and write a test harness as an IO action that calls each method and prints the result.
inductive HttpReq where
| GET  (uri : String) (ver : String) : HttpReq
| POST (uri : String) (ver : String) : HttpReq
| PUT  (uri : String) (ver : String) : HttpReq

structure HttpResp where
  status : Nat
  body   : String
deriving Repr

def resp := HttpResp.mk 200 "some html"
#eval resp
