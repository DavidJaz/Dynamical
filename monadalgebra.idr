module monadalgebra

import Control.Monad.Identity

public export
interface (Monad m) => MonadAlgebra (m : Type -> Type) a where
  eval : m a -> a

export
implementation MonadAlgebra Identity a where
  eval (Id a) = a

export
implementation (Monad m) => MonadAlgebra m (m a) where
  eval = join

