module Model where

import Data.Functor.Identity
import Distribution (Dist, DistT)
import qualified Distribution as D
import Control.Monad.Trans.Class

-- |Models of samples from distributions.
class Model domain a where
  laplace  :: a -> Double -> domain a
  gaussian :: a -> Double -> domain a

instance (MonadTrans t) => Model (t Dist) Double where
  laplace c w = lift $ D.laplace c w
  gaussian c w = lift $ D.gaussian c w

instance (Applicative f) => Model (DistT f) Double where
  laplace  = D.laplace
  gaussian = D.gaussian

newtype NoRandomness a = NoRandomness { unwrapNoRandomness :: a }
  deriving (Functor)

instance Applicative NoRandomness where
  pure = NoRandomness
  f <*> a = NoRandomness $ (unwrapNoRandomness f) (unwrapNoRandomness a)

instance Monad NoRandomness where
  return = pure
  a >>= f = f (unwrapNoRandomness a)

instance Model NoRandomness Double where
  laplace c _ = NoRandomness c
  gaussian c _ = NoRandomness c

instance (MonadTrans t) => Model (t NoRandomness) Double where
  laplace c _ = lift $ NoRandomness c
  gaussian c _ = lift $ NoRandomness c
