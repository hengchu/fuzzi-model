module Symbol where

import Data.SBV
import Types
import Control.Monad.State.Strict

newtype RealExpr = RealExpr { unwrapRealExpr :: SReal }
  deriving (Show, Eq, Num, Fractional)
newtype BoolExpr = BoolExpr { unwrapBoolExpr :: SBool }
  deriving (Show, Eq)

type FreshSymbolic = StateT Int Symbolic

symTrue :: BoolExpr
symTrue = BoolExpr sTrue

symFalse :: BoolExpr
symFalse = BoolExpr sFalse

and :: BoolExpr -> BoolExpr -> BoolExpr
and a b = BoolExpr $ (unwrapBoolExpr a) .&& (unwrapBoolExpr b)

or :: BoolExpr -> BoolExpr -> BoolExpr
or a b = BoolExpr $ (unwrapBoolExpr a) .|| (unwrapBoolExpr b)

is :: BoolExpr -> BoolExpr -> BoolExpr
is a b = BoolExpr $ (unwrapBoolExpr a) .== (unwrapBoolExpr b)

neg :: BoolExpr -> BoolExpr
neg a = BoolExpr $ sNot (unwrapBoolExpr a)

isnot :: BoolExpr -> BoolExpr -> BoolExpr
isnot a b = neg $ a `is` b

mkRealSymbol :: String -> FreshSymbolic RealExpr
mkRealSymbol name = do
  counter <- get
  modify (+1)
  lift $ RealExpr <$> sReal (name ++ show counter)

instance Value RealExpr
instance Value BoolExpr
