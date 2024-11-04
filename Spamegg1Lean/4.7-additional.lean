structure Tree : Type where
  latinName : String
  commonNames : List String

-- three equivalent syntax sugars for structure instances
def oak : Tree :=
  ⟨"Quercus robur", ["common oak", "European oak"]⟩

def birch : Tree :=
  { latinName := "Betula pendula",
    commonNames := ["silver birch", "warty birch"]
  }

def sloe : Tree where
  latinName := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]

-- typeclasses also have the same 3 sugars
class Display (α : Type) where
  displayName : α → String

instance : Display Tree :=
  ⟨Tree.latinName⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

instance : Display Tree where
  displayName t := t.latinName

-- examples are anonymous defs
example (n : Nat) (k : Nat) : Bool := -- this fun cannot be called
  n + k == k + n
