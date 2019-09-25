module Data.Fuzzi.Rosette where

import Prelude hiding (and)
import Control.Monad
import Data.Functor.Compose
import Data.Fuzzi.EDSL
import Data.Fuzzi.Symbol
import Data.Fuzzi.Types

type GuardedSymbolicUnion = Compose SymbolicUnion Guarded

-- eval :: Fuzzi a -> GuardedSymbolicUnion a
-- eval (Return a)  = return . eval $ a
-- eval (Bind ma f) = do
--   points {- Eval a -} <- eval ma
--   eval (f (Lit points))

singleton :: a -> SymbolicUnion a
singleton = Singleton

guarded :: a -> Guarded a
guarded = MkGuarded (bool True)

class Symbolic a where
  type SymbolicVal a :: *
  into  :: a -> GuardedSymbolicUnion (SymbolicVal a)
  merge :: Guarded a -> GuardedSymbolicUnion (SymbolicVal a) -> GuardedSymbolicUnion (SymbolicVal a)

newtype IntExpr = IntExpr { getIntExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord)

data Guarded (a :: *) where
  MkGuarded :: BoolExpr -> a -> Guarded a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data SymbolicUnion (a :: *) where
  Singleton :: a -> SymbolicUnion a
  Union     :: SymbolicUnion a -> SymbolicUnion a -> SymbolicUnion a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Applicative Guarded where
  pure = guarded
  (MkGuarded cond1 f) <*> (MkGuarded cond2 a) =
    MkGuarded (cond1 `and` cond2) (f a)

instance Applicative SymbolicUnion where
  pure = Singleton
  (Singleton f)   <*> (Singleton a)   = Singleton (f a)
  (Singleton f)   <*> (u1 `Union` u2) = (fmap f u1) `Union` (fmap f u2)
  (f1 `Union` f2) <*> (Singleton a)   = (fmap ($ a) f1) `Union` (fmap ($ a) f2)
  (f1 `Union` f2) <*> (u1 `Union` u2) =
    (f1 <*> u1) `Union` (f1 <*> u2) `Union` (f2 <*> u1) `Union` (f2 <*> u2)
