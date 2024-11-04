def hello := "Hello"
def lean : String := "Lean"
#eval String.append hello (String.append " " lean)

def add1 (n : Nat) : Nat := n + 1
#eval add1 7

def maximum (n : Nat) (k : Nat) : Nat := if n < k then k else n
#eval maximum (5 + 8) (2 * 7)
#check (maximum) -- Nat -> Nat -> Nat

-- Define the function joinStringsWith with type String -> String -> String -> String
-- that creates a new string by placing its first argument between its second and third.
-- joinStringsWith ", " "one" "and another" should evaluate to "one, and another".
def joinStringsWith (s1 : String) (s2 : String) (s3 : String) : String :=
  String.append s2 (String.append s1 s3)

-- What is the type of joinStringsWith ": "? Check your answer with Lean.
#check (joinStringsWith)

-- Define a function volume with type Nat → Nat → Nat → Nat
-- that computes the volume of a rectangular prism with the given height, width, and depth
def volume (width : Nat) (height : Nat) (depth : Nat) : Nat :=
  width * height * depth

def Str : Type := String
def aStr : Str := "This is a string."

def NaturalNumber : Type := Nat
-- def thirtyEight : NaturalNumber := 38 -- error b/c overloading allowed
def thirtyEight : NaturalNumber := (38 : Nat) -- OK

abbrev N : Type := Nat
def thirtyNine : N := 39
