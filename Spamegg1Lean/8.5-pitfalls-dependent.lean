def Nat.plusL : Nat → Nat → Nat
  | 0, k     => k
  | n + 1, k => plusL n k + 1

def Nat.plusR : Nat → Nat → Nat
  | n, 0     => n
  | n, k + 1 => plusR n k + 1

inductive Vect (α : Type u) : Nat → Type u where
  | nil  : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
deriving Repr

def appendL0 : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys       => sorry
  | .cons x xs, ys => sorry

def appendL1 : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, _, .nil, ys           => ys
  | n + 1, k, .cons x xs, ys => .cons x (appendL1 n k xs ys)

def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys       => ys
  | .cons x xs, ys => .cons x (appendL xs ys)

def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0     => by rfl
  | k + 1 => congrArg (· + 1) (plusR_zero_left k)

def plusR_succ_left (n : Nat) : (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0     => by rfl
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)

def appendR0 : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys           => plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys => plusR_succ_left n k ▸ .cons x (appendR0 n k xs ys)

def appendR : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys       => plusR_zero_left _ ▸ ys
  | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR xs ys)

-- Using a recursive function in the style of plusR_succ_left,
-- prove that for all Nats n and k, n.plusR k = n + k.

-- Write a function on Vect for which plusR is more natural than plusL,
-- where plusL would require proofs to be used in the definition.
