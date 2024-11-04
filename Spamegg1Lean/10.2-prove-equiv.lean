def NonTail.sum : List Nat → Nat
  | []      => 0
  | x :: xs => x + sum xs

def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | []      => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat := Tail.sumHelper 0 xs

theorem helper_add_sum_accum (xs : List Nat) (n : Nat)
  : n + Tail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil          => rfl
  | cons y ys ih => sorry
    -- simp [Tail.sum, Tail.sumHelper]
    -- rw [Tail.sum] at ih -- STUCK!!!

-- this attempt gets stuck.
theorem non_tail_sum_eq_tail_sum_stuck : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil          => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
    rw [ih]
    exact helper_add_sum_accum ys y

-- more elegant proof
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs :=
  by induction xs with
  | nil          => intro n; rfl
  | cons y ys ih =>
    intro n
    simp [Tail.sumHelper, NonTail.sum]
    rw [<- Nat.add_assoc, Nat.add_comm y n]
    exact ih (n + y)

theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [<- Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0

-- Warming Up
-- Write your own proofs for Nat.zero_add, Nat.add_assoc, and Nat.add_comm
-- using the induction tactic.
theorem Nat.zero_add1 (n : Nat) : 0 + n = n :=
  by induction n with
  | zero => simp
  | succ => simp

theorem Nat.add_assoc1 (n m k : Nat) : n + m + k = n + (m + k) :=
  by induction k with
  | zero => simp
  | succ => simp_arith

theorem Nat.add_comm1 (n m : Nat) : n + m = m + n :=
  by induction n with
  | zero => simp
  | succ => simp_arith

-- More Accumulator Proofs
-- Reversing Lists
def NonTail.reverse : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]
def Tail.reverseHelper (soFar : List α) : List α → List α
  | []      => soFar
  | x :: xs => reverseHelper (x :: soFar) xs
def Tail.reverse (xs : List α) : List α := Tail.reverseHelper [] xs
-- Adapt the proof for sum into a proof for NonTail.reverse and Tail.reverse.
-- The first step is to think about the relationship between the accumulator value
-- being passed to Tail.reverseHelper and the non-tail-recursive reverse.
-- Just as adding a number to the accumulator in Tail.sumHelper is the same
-- as adding it to the overall sum, using List.cons to add a new entry to the
-- accumulator in Tail.reverseHelper is equivalent to some change to the overall result.
-- Try three or four different accumulator values with pencil and paper until the
-- relationship becomes clear. Use this relationship to prove a suitable helper theorem.
-- Then, write down the overall theorem. Because NonTail.reverse and Tail.reverse are
-- polymorphic, stating their equality requires the use of @ to stop Lean from trying
-- to figure out which type to use for α. Once α is treated as an ordinary argument,
-- funext should be invoked with both α and xs:
theorem non_tail_reverse_eq_helper_accum (xs : List α) :
    (acc : List α) → NonTail.reverse xs ++ acc = Tail.reverseHelper acc xs :=
  by induction xs with
  | nil          => simp [NonTail.reverse, Tail.reverseHelper]
  | cons y ys ih =>
    intro acc
    simp [Tail.reverseHelper, NonTail.reverse]
    exact ih (y :: acc)

theorem non_tail_reverse_eq_tail_reverse : @NonTail.reverse = @Tail.reverse := by
  funext α xs
  simp [Tail.reverse]
  rw [<- List.append_nil (NonTail.reverse xs)]
  exact non_tail_reverse_eq_helper_accum xs []

-- Factorial
def NonTail.factorial : Nat → Nat
  | 0     => 1
  | n + 1 => factorial n * (n + 1)
def Tail.factorialHelper : Nat → Nat → Nat
  | 0, acc     => acc
  | n + 1, acc => factorialHelper n (acc * (n + 1))
def Tail.factorial (n : Nat) : Nat := Tail.factorialHelper n 1
-- Prove that NonTail.factorial from the exercises in the previous section is
-- equal to your tail-recursive solution by finding the relationship between
-- the accumulator and the result and proving a suitable helper theorem.
theorem non_tail_factorial_eq_helper_accum (n : Nat) :
    (acc : Nat) → (NonTail.factorial n) * acc = Tail.factorialHelper n acc :=
  by induction n with
  | zero      => simp [NonTail.factorial, Tail.factorialHelper]
  | succ m ih =>
    intro acc
    simp [Tail.factorialHelper, NonTail.factorial]
    rw [Nat.mul_assoc, Nat.mul_comm acc (m + 1)]
    exact ih ((m + 1) * acc)

theorem non_tail_fact_eq_tail_fact : @NonTail.factorial = @Tail.factorial := by
  funext n
  simp [Tail.factorial]
  rw [<- Nat.mul_one (NonTail.factorial n)]
  exact non_tail_factorial_eq_helper_accum n 1
