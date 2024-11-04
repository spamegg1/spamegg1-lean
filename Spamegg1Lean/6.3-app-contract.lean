-- pure id <*> v = v
-- pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)
-- pure f <*> pure x = pure (f x)
-- u <*> pure x = pure (fun f => f x) <*> u

-- all applicatives are functors
def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x

-- Alternate implementation by extending Functor
-- class Applicative (f : Type → Type) extends Functor f where
--   pure : α → f α
--   seq  : f (α → β) → (Unit → f α) → f β
--   map g x := seq (pure g) (fun () => x)

-- all monads are applicatives
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)

-- Alternate implementation by extending Applicative
-- class Monad (m : Type → Type) extends Applicative m where
--   bind : m α → (α → m β) → m β
--   seq f x :=
--     bind f fun g =>
--     bind (x ()) fun y =>
--     pure (g y)
