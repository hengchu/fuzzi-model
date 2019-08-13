module Model where

import Data.Functor.Identity
import Distribution (Dist, DistT)
import qualified Distribution as D
import Control.Monad.Trans.Class
import Types
import Data.SBV
import Symbol
import Data.Coerce

infix 4 %<, %<=, %>, %>=, %==, %/=

class ModelOrd a where
  type CmpResult a :: *

  (%<)  :: a -> a -> CmpResult a
  (%<=) :: a -> a -> CmpResult a
  (%>)  :: a -> a -> CmpResult a
  (%>=) :: a -> a -> CmpResult a
  (%==) :: a -> a -> CmpResult a
  (%/=) :: a -> a -> CmpResult a

instance ModelOrd Double where
  type CmpResult Double = Bool

  (%<)  = (<)
  (%<=) = (<=)
  (%>)  = (>)
  (%>=) = (>=)
  (%==) = (==)
  (%/=) = (/=)

instance ModelOrd RealExpr where
  type CmpResult RealExpr = BoolExpr

  (%<)  a b = BoolExpr $ (.<)  (unwrapRealExpr a) (unwrapRealExpr b)
  (%<=) a b = BoolExpr $ (.<=) (unwrapRealExpr a) (unwrapRealExpr b)
  (%>)  a b = BoolExpr $ (.>)  (unwrapRealExpr a) (unwrapRealExpr b)
  (%>=) a b = BoolExpr $ (.>=) (unwrapRealExpr a) (unwrapRealExpr b)
  (%==) a b = BoolExpr $ (.==) (unwrapRealExpr a) (unwrapRealExpr b)
  (%/=) a b = BoolExpr $ (./=) (unwrapRealExpr a) (unwrapRealExpr b)

-- |Models of samples from distributions.
class (Monad domain, Fractional a, Value a, ModelOrd a) => Model domain a where
  laplace  :: a -> Double -> domain a
  gaussian :: a -> Double -> domain a

instance (MonadTrans t, Monad (t Dist)) => Model (t Dist) Double where
  laplace c w = lift $ D.laplace c w
  gaussian c w = lift $ D.gaussian c w

instance (Monad f) => Model (DistT f) Double where
  laplace  = D.laplace
  gaussian = D.gaussian

newtype NoRandomness a = NoRandomness { unwrapNoRandomness :: a }
  deriving (Functor)

instance Applicative NoRandomness where
  pure = NoRandomness
  f <*> a = NoRandomness $ unwrapNoRandomness f (unwrapNoRandomness a)

instance Monad NoRandomness where
  return = pure
  a >>= f = f (unwrapNoRandomness a)

instance Model NoRandomness Double where
  laplace c _ = NoRandomness c
  gaussian c _ = NoRandomness c

instance (MonadTrans t, Monad (t NoRandomness)) => Model (t NoRandomness) Double where
  laplace c _ = lift $ NoRandomness c
  gaussian c _ = lift $ NoRandomness c

instance (MonadTrans t, Monad (t FreshSymbolic)) => Model (t FreshSymbolic) RealExpr where
  laplace  _ _ = lift $ mkRealSymbol "lap"
  gaussian _ _ = lift $ mkRealSymbol "gauss"

data BinOp = PLUS | MINUS | MULT | DIV
  deriving (Show, Eq, Ord)
data UnOp  = NEG  | ABS   | SIGN
  deriving (Show, Eq, Ord)

data WithDistribution a where
  Pure     :: a -> WithDistribution a
  Laplace  :: a -> WithDistribution a -> Double -> WithDistribution a
  Gaussian :: a -> WithDistribution a -> Double -> WithDistribution a
  Bin      :: a -> WithDistribution a -> BinOp -> WithDistribution a -> WithDistribution a
  Un       :: a -> UnOp -> WithDistribution a -> WithDistribution a
  deriving (Show, Eq, Ord, Functor)

getSample :: WithDistribution a -> a
getSample (Pure v) = v
getSample (Laplace v _ _) = v
getSample (Gaussian v _ _) = v
getSample (Bin v _ _ _) = v
getSample (Un v _ _) = v

inject :: a -> WithDistribution a
inject = Pure

instance Num a => Num (WithDistribution a) where
  lhs + rhs     = Bin (getSample lhs + getSample rhs) lhs PLUS rhs
  lhs * rhs     = Bin (getSample lhs * getSample rhs) lhs MULT rhs
  abs v         = Un (abs $ getSample v) ABS  v
  signum v      = Un (signum $ getSample v) SIGN v
  negate v      = Un (negate $ getSample v) NEG  v
  fromInteger v = Pure $ fromInteger v

instance Fractional a => Fractional (WithDistribution a) where
  fromRational v = Pure $ fromRational v
  lhs / rhs      = Bin (getSample lhs / getSample rhs) lhs DIV rhs

instance (Model domain a) => Model domain (WithDistribution a) where
  laplace c w = do
    sample <- laplace @domain @a (getSample c) w
    return $ Laplace sample c w
  gaussian c w = do
    sample <- gaussian @domain @a (getSample c) w
    return $ Gaussian sample c w

instance ModelOrd a => ModelOrd (WithDistribution a) where
  type CmpResult (WithDistribution a) = CmpResult a

  (%<)  a b = (%<)  (getSample a) (getSample b)
  (%<=) a b = (%<=) (getSample a) (getSample b)
  (%>)  a b = (%>)  (getSample a) (getSample b)
  (%>=) a b = (%>=) (getSample a) (getSample b)
  (%==) a b = (%==) (getSample a) (getSample b)
  (%/=) a b = (%/=) (getSample a) (getSample b)

instance Value a => Value (WithDistribution a)
