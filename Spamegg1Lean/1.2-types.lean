#eval (1 + 2 : Nat)
#eval 1 - 2 -- 0 because Nat = {0, 1, 2, ...}
#eval (1 - 2 : Int) -- -1 because Int = Z
#check (1 - 2 : Int)
-- #check String.append "hello" [" ", "world"] -- error
