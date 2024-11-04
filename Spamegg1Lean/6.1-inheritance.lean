structure MythicalCreature where
  large : Bool
deriving Repr

#check MythicalCreature.mk
#check MythicalCreature.large -- takes "self" as argument!

structure Monster extends MythicalCreature where
  vulnerability : String -- now it has two fields: large and vuln.
deriving Repr

#check Monster.mk

def troll : Monster where
  large         := true
  vulnerability := "sunlight"
#eval troll.toMythicalCreature -- large=true

def troll2 : Monster := {large := true, vulnerability := "sunlight"}
-- def troll3 : Monster := ⟨true, "sunlight"⟩ -- error
def troll3 : Monster := ⟨MythicalCreature.mk true, "sunlight"⟩ -- OK
def troll4 : Monster := ⟨⟨true⟩, "sunlight"⟩ -- OK

-- #eval MythicalCreature.large troll -- error
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large

-- multiple inheritance
structure Helper extends MythicalCreature where
  assistance : String
  payment    : String -- now it has 3 fields
deriving Repr
#check Helper.mk -- takes MyCr, assistance, payment

def nisse : Helper where
  large      := false
  assistance := "household tasks"
  payment    := "porridge"

-- now it has 4 fields
structure MonstrousAssistant extends Monster, Helper where
deriving Repr
#check MonstrousAssistant.mk -- takes a Monster, assistance, payment

def domesticatedTroll : MonstrousAssistant where
  large         := false
  assistance    := "heavy labor"
  payment       := "toy goats"
  vulnerability := "sunlight"

#print MonstrousAssistant.toHelper

-- default declarations
inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size  : Size
  large := size == Size.large

def nonsenseCreature : SizedCreature where
  large := false
  size := .large

-- #eval nonsenseCreature -- error
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)

def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by decide
