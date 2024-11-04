#eval "Hello!!!".dropRightWhile (· == '!')
#eval "Hello...   ".dropRightWhile (fun c => not (c.isAlphanum))

def twice (action : IO Unit) : IO Unit := do
  action
  action

#eval twice (IO.println "shy")

def nTimes (action : IO Unit) : Nat → IO Unit
  | 0     => pure ()
  | n + 1 => do
    action
    nTimes action n

#eval nTimes (IO.println "Hello") 3

def countdown : Nat → List (IO Unit)
  | 0     => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def from5 : List (IO Unit) := countdown 5

def runActions : List (IO Unit) → IO Unit
  | []             => pure ()
  | act :: actions => do
    act
    runActions actions

-- def main : IO Unit := runActions from5

-- Step through the execution of the following program on a piece of paper:
-- lean --run Spamegg1Lean/2.2-step.lean
def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting
