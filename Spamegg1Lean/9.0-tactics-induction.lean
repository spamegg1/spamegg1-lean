def Nat.plusR : Nat → Nat → Nat -- from before
  | n, 0     => n
  | n, k + 1 => plusR n k + 1

theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR] <;> assumption
  -- induction k
  -- case zero      => rfl
  -- case succ n ih => simp [Nat.plusR]; assumption
  -- induction k with
  -- | zero      => rfl
  -- | succ n ih => simp [Nat.plusR]; assumption
  -- | succ n ih => simp [Nat.plusR]; exact ih
  -- | succ n ih => unfold Nat.plusR; rw [<- ih]

inductive BinTree (α : Type) where -- from before
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf         => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)

def BinTree.count : BinTree α → Nat
  | .leaf         => 0
  | .branch l _ r => 1 + l.count + r.count

theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
  induction t with
  | leaf                 => rfl
  | branch l _ r ihl ihr => simp_arith [BinTree.mirror, BinTree.count, *]


-- Prove plusR_succ_left using the induction ... with tactic.
theorem plusR_succ_left1 (n : Nat) (k : Nat)
  : Nat.plusR (n + 1) k = Nat.plusR n k + 1 :=
  by induction k with
  | zero      => rfl
  | succ m ih => simp [Nat.plusR, ih]

-- Rewrite the proof of plus_succ_left to use <;> in a single line.
theorem plusR_succ_left2 (n : Nat) (k : Nat)
  : Nat.plusR (n + 1) k = Nat.plusR n k + 1 :=
  by induction k <;> simp [Nat.plusR, *]

-- Prove that appending lists is associative using induction on lists:
theorem List.append_assoc1 (xs ys zs : List α) : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
  by induction zs <;> simp
