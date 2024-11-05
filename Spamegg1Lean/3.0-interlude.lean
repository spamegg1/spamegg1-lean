def woodlandCritters : List String := ["hedgehog", "deer", "snail"]

def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]
-- def oob := woodlandCritters[3] -- error, out of bounds

def onePlusOneIsTwo : 1 + 1 = 2 := rfl -- true
-- def onePlusOneIsFifteen : 1 + 1 = 15 := rfl -- error because false
def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwoThm : OnePlusOneIsTwo := rfl
theorem onePlusOneIsTwoTactics : 1 + 1 = 2 := by simp

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by decide

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

-- def third (xs : List α) : α := xs[2] -- error, list must have length at least 3
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
#eval third woodlandCritters (by decide) -- snail

def thirdOption (xs : List α) : Option α := xs[2]?
#eval thirdOption woodlandCritters -- some snail
#eval thirdOption ["only", "two"] -- none
#eval woodlandCritters[1]! -- crashes if oob

-- def unsafeThird (xs : List α) : α := xs[2]! -- polymorphic fun uses unsafe indexing

-- Prove the following theorems using rfl:
-- 2 + 3 = 5, 15 - 8 = 7, "Hello, ".append "world" = "Hello, world".
-- What happens if rfl is used to prove 5 < 18? Why?
theorem twoPlusThreeIsFive : (2 + 3 = 5) := by rfl
theorem fifteenMinusEight : (15 - 8 = 7) := by rfl
theorem helloAppendWorld : ("Hello, ".append "world" = "Hello, world") := by rfl
-- theorem fiveLessEighteen : (5 < 18) := by rfl -- error
theorem fiveLessEighteen : (5 < 18) := by decide

-- Prove the following theorems using by simp:
-- 2 + 3 = 5, 15 - 8 = 7, "Hello, ".append "world" = "Hello, world", 5 < 18.
theorem twoPlusThreeIsFive2 : (2 + 3 = 5) := by simp
theorem fifteenMinusEight2 : (15 - 8 = 7) := by simp
theorem helloAppendWorld2 : ("Hello, ".append "world" = "Hello, world") := by decide

-- Write a function that looks up the fifth entry in a list.
-- Pass the evidence that this lookup is safe as an argument to the function.
def fifth (xs : List α) (ok : xs.length >= 5) : α := xs[4]
#eval fifth [1,2,3,4,5] (by simp) -- 5
