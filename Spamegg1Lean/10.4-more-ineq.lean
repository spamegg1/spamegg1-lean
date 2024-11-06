-- Lean built-in
-- structure And (a b : Prop) : Prop where
--   intro ::
--   left : a
--   right : b

def merge [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _                => ys
  | _, []                => xs
  | x' :: xs', y' :: ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    | .gt       => y' :: merge (x'::xs') ys'
termination_by xs.length + ys.length
-- termination_by (xs, ys) -- also OK, due to WellFoundedRelation

def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | []      => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)

-- Lean built-in, renamed
theorem Nat.succ_le_succ1 : n ≤ m → Nat.succ n ≤ Nat.succ m := by
  intro h
  induction h with
  | refl      => constructor
  | step _ ih => constructor; assumption
theorem Nat.succ_le_succ2 : n ≤ m → Nat.succ n ≤ Nat.succ m -- different way to write it
  | .refl    => .refl
  | .step h' => .step (Nat.succ_le_succ2 h')
theorem Nat.le_succ_of_le1 : n ≤ m → n ≤ Nat.succ m := by -- also built-in
  intro h
  induction h with
  | refl => constructor; constructor
  | step => constructor; assumption
theorem Nat.le_succ_of_le2 : n ≤ m → n ≤ Nat.succ m := by -- more detailed
  intro h
  induction h with
  | refl      => apply Nat.le.step; exact Nat.le.refl
  | step _ ih => apply Nat.le.step; exact ih
theorem Nat.le_succ_of_le3 (h : n ≤ m) : n ≤ Nat.succ m := by -- golfed
  induction h <;> repeat (first | constructor | assumption)
theorem Nat.le_succ_of_le4 : n ≤ m → n ≤ Nat.succ m -- recursive function
  | .refl   => .step .refl
  | .step h => .step (Nat.le_succ_of_le h)

theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil          => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left  => assumption
    case right => apply Nat.le_succ_of_le; assumption

theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs => simp_arith [splitList]; apply splitList_shorter_le

theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right

def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | []  => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := by apply Nat.ge_of_not_lt; assumption
    have : halves.fst.length < xs.length := by apply splitList_shorter_fst; assumption
    have : halves.snd.length < xs.length := by apply splitList_shorter_snd; assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length

#eval mergeSort ["soapstone", "geode", "mica", "limestone"]
#eval mergeSort [5, 3, 22, 15]

def div (n k : Nat) (ok : k > 0) : Nat := if n < k then 0 else 1 + div (n - k) k ok

def div2 (n k : Nat) (ok : k > 0) : Nat :=
  if h : n < k then 0
  else
    have : 0 < n := by
      cases n with
      | zero    => contradiction
      | succ n' => simp_arith
    have : n - k < n := by apply Nat.sub_lt <;> assumption
    1 + div (n - k) k ok
-- termination_by div2 n k ok => n -- unused, fun is not recursive

-- EXERCISES
-- NOTE: These exercises give no indication whatsoever about what CAN be used.
-- Most of them can be done with simp or simp_arith, which makes them trivial.
-- They can also be done by using Nat built-in proofs, which defeats the purpose.
-- I also don't know how to manually apply defs of <, <=, +, -.
-- I wish more details were given...

-- Prove the following theorems:
-- For all natural numbers n, 0 < n+1
theorem ex1 (n : Nat) : 0 < n + 1 := by
  induction n with
  | zero      => exact Nat.zero_lt_one
  | succ k ih => exact Nat.lt_trans ih (Nat.lt_add_one (k + 1))

-- For all natural numbers n, 0 ≤ n
theorem ex2 (n : Nat) : 0 ≤ n := by
  induction n with
  | zero      => exact Nat.le_of_eq rfl
  | succ k ih => exact Nat.le_trans ih (Nat.le_add_right k 1)

-- For all natural numbers n, n − n = 0
theorem ex3 (n : Nat) : n - n = 0 := by
  induction n with
  | zero      => rfl
  | succ k ih => rw [Nat.add_comm, Nat.sub_add_eq, Nat.add_comm]; exact ih

-- For all natural numbers n,k, (n + 1) − (k + 1) = n − k
theorem ex4 (n k : Nat) : (n + 1) - (k + 1) = n - k := by
  induction k with
  | zero      => rfl
  | succ _ ih => rw [Nat.sub_add_eq, ih, Nat.sub_add_eq]

-- For all natural numbers n,k, if k < n then n ≠ 0
theorem ex5 (n k : Nat) (h : k < n) : n ≠ 0 := by
  induction k with
  | zero      => apply Nat.not_eq_zero_of_lt h
  | succ a ih =>
    have g : a < a + 1 := by apply Nat.lt_add_one
    exact ih (Nat.lt_trans g h)

-- For all natural numbers n,k, if n + 1 < k then n < k
theorem ex6 (n k : Nat) (h : n + 1 < k) : n < k := by
  have g : n < n + 1 := by apply Nat.lt_add_one
  exact Nat.lt_trans g h
