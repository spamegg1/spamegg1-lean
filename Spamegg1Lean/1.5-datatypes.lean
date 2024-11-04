inductive MyBool where
  | false : MyBool
  | true  : MyBool

inductive MyNat where
  | zero             : MyNat
  | succ (n : MyNat) : MyNat

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ _ => false

#eval isZero Nat.zero

#eval Nat.pred 839
#eval Nat.pred 0 -- 0

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

#eval pred 839

structure Point3D where
  x : Float
  y : Float
  z : Float

def depth (p : Point3D) : Float :=
  match p with
  | { x:= _, y := _, z := d } => d

#eval depth { x := 1, y := 2, z := 3 } -- 3.0

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ k => not (even k)

#eval even 1000 -- stack overflow at 10000

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => Nat.succ (plus n k')

#eval plus 10 100

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => pred (minus n k')

-- fails to infer structural recursion
-- requires manual proof of termination
-- def div (n : Nat) (k : Nat) : Nat :=
--   if n < k then 0 else Nat.succ (div (n - k) k)
