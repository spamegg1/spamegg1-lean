-- 1. A definition or datatype T that takes a monad as an argument.
-- It should have a type like (Type u → Type v) → Type u → Type v,
-- though it may accept additional arguments prior to the monad.

-- 2. A Monad instance for T m that relies on an instance of Monad m.
-- This enables the transformed monad to be used as a monad.

-- 3. A MonadLift instance that translates actions of type m α into
-- actions of type T m α, for arbitrary monads m.
-- This enables actions from the underlying monad to be used in the transformed monad.
