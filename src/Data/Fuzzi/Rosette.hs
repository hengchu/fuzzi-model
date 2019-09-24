module Data.Fuzzi.Rosette where

import Control.Monad
import Data.Fuzzi.EDSL
import Data.Fuzzi.Symbol

-- need to be able to "map" over the evaluation results
type family Eval (a :: *) where
  Eval (m a) = m (Eval a)
  Eval a     = SymbolicUnion (Guarded a)

eval :: Fuzzi a -> Eval a
eval (Return a)  = return . eval $ a
eval (Bind ma f) = do
  points {- Eval a -} <- eval ma
  eval (f (Lit points))

singleton :: a -> SymbolicUnion a
singleton = Singleton

guarded :: a -> Guarded a
guarded = MkGuarded (bool True)

newtype IntExpr = IntExpr { getIntExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord)

data Guarded (a :: *) where
  MkGuarded :: BoolExpr -> a -> Guarded a
  deriving (Show, Eq, Ord, Functor)

data SymbolicUnion (a :: *) where
  Singleton :: a -> SymbolicUnion a
  Union     :: SymbolicUnion a -> SymbolicUnion a -> SymbolicUnion a
  deriving (Show, Eq, Ord, Functor)

class SymbolicMerge a where
  merge :: Guarded a -> Guarded a -> (SymbolicUnion (Guarded a))
