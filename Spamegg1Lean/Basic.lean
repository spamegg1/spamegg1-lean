def hello := "world"

inductive Palindrome: List T -> Prop where
  | nil      : Palindrome []
  | single   : (t : T) -> Palindrome [t]
  | sandwich : (t : T) -> Palindrome ts -> Palindrome ([t] ++ ts ++ [t])

theorem palindrome_reverse(h: Palindrome ts) : Palindrome ts.reverse := by
  induction h with
    | nil             => exact Palindrome.nil
    | single t        => exact Palindrome.single t
    | sandwich t h ih => simp ; exact Palindrome.sandwich _ ih

theorem reverse_eq_of_palindrome(h: Palindrome ts) : ts = ts.reverse := by
  induction h with
    | nil             => rfl
    | single t        => rfl
    | sandwich t h ih => simp; exact ih

example (h : Palindrome ts) : Palindrome ts.reverse := by
  rw [reverse_eq_of_palindrome h]
  simp
  exact h
