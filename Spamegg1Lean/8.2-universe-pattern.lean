inductive NatOrBool where | nat | bool

abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat  => Nat
  | .bool => Bool

def decode (t : NatOrBool) (input : String) : Option t.asType :=
  match t with
  | .nat  => input.toNat?
  | .bool =>
    match input with
    | "true"  => some true
    | "false" => some false
    | _       => none

#eval decode NatOrBool.nat "5" -- some 5
#eval decode NatOrBool.nat "hello" -- none
#eval decode NatOrBool.bool "true" -- some true
#eval decode NatOrBool.bool "false" -- some false
#eval decode NatOrBool.bool "hello" -- none

inductive NestedPairs where
  | nat  : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs

abbrev NestedPairs.asType : NestedPairs → Type
  | .nat        => Nat
  | .pair t1 t2 => asType t1 × asType t2

def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat        => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

instance {t : NestedPairs} : BEq t.asType where
  beq x y := t.beq x y

inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr  : Finite → Finite → Finite

abbrev Finite.asType : Finite → Type
  | .unit       => Unit
  | .bool       => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr t1 t2  => asType t1 → asType t2

def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse

mutual
def Finite.enumerate (t : Finite) : List t.asType :=
  match t with
  | .unit       => [()]
  | .bool       => [true, false]
  | .pair t1 t2 => t1.enumerate.product t2.enumerate
  | .arr t1 t2  => t1.functions t2.enumerate

def Finite.functions (t : Finite) (results : List α) : List (t.asType → α) :=
  match t with
  | .unit => results.map fun r => fun () => r
  | .bool =>
    (results.product results).map fun (r1, r2) =>
      fun
      | true  => r1
      | false => r2
  | .pair t1 t2 =>
    let f1s := t1.functions <| t2.functions results
    f1s.map fun f => fun (x, y) => f x y
  | .arr t1 t2  =>
    let args := t1.enumerate
    let base := results.map fun r => fun _ => r
    args.foldr (fun arg rest =>
      (t2.functions rest).map fun more =>
        fun f => more (f arg) f)
      base
end

def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .unit       => true
  | .bool       => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr t1 t2  => t1.enumerate.all fun arg => beq t2 (x arg) (y arg)


-- Write a function that converts any value from a type coded for by
-- Finite into a string. Functions should be represented as their tables.

-- Add the empty type Empty to Finite and Finite.beq.

-- Add Option to Finite and Finite.beq.
