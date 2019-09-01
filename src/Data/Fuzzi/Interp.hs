{- HLINT ignore "Redundant bracket" -}

module Data.Fuzzi.Interp where

import Data.Proxy
import Prelude hiding (and, or)
import Data.Fuzzi.IfCxt
import Data.Fuzzi.EDSL
import Data.Fuzzi.Types
import Type.Reflection hiding (App)
import Control.Monad.Catch

newtype AbortException = AbortException {
  getAbortReason :: String
  } deriving (Show, Eq, Ord)

instance Exception AbortException

eval :: forall a. Fuzzi a -> a
eval (Lam f) = eval . f . Lit
eval (App f a) = (eval f) (eval a)
eval (Return a) = return (eval a)
eval (Sequence a b) = eval a >> (eval b)
eval (Bind a f) = eval a >>= (eval . f . Lit)
eval (Lit a) = a
eval (If cond t f) = if toBool (eval cond) then eval t else eval f
eval (IfM (cond :: Fuzzi bool) t f) =
  ifCxt (Proxy :: Proxy (ConcreteBoolean bool))
        (if toBool (eval cond) then eval t else eval f)
        (error ("The type "
                ++ show (typeRep @bool)
                ++ " does not support concrete execution"))
eval (Laplace _ c w) = laplace (eval c) w
eval (Gaussian _ c w) = gaussian (eval c) w
eval (Variable v) =
  error ("unexpected variable " ++ show v ++ " :: " ++ show (typeRep @a))
eval (PrettyPrintVariable v) =
  error ("unexpected variable " ++ v ++ " :: " ++ show (typeRep @a))
eval (And a b) = and (eval a) (eval b)
eval (Or a b) = or (eval a) (eval b)
eval (Not a) = neg (eval a)
eval (Add a b) = (eval a) + (eval b)
eval (Mult a b) = (eval a) * (eval b)
eval (Sub a b) = (eval a) - (eval b)
eval (Sign a) = signum (eval a)
eval (Abs a) = abs (eval a)
eval (Div a b) = (eval a) / (eval b)
eval (IDiv a b) = (eval a) `idiv` (eval b)
eval (IMod a b) = (eval a) `imod` (eval b)
eval (Lt a b) = (eval a) %< (eval b)
eval (Le a b) = (eval a) %<= (eval b)
eval (Gt a b) = (eval a) %> (eval b)
eval (Ge a b) = (eval a) %>= (eval b)
eval (Eq_ a b) = (eval a) %== (eval b)
eval (Neq a b) = (eval a) %/= (eval b)
eval (AssertTrueM cond) =
  assertTrue (eval cond)
eval (AssertFalseM cond) =
  assertFalse (eval cond)
eval ListNil         = []
eval (ListCons x xs) = (eval x):(eval xs)
eval (ListSnoc xs x) = (eval xs) ++ [eval x]
eval (ListIsNil xs)  = fromBool $ null (eval xs)
eval (ListLength xs) = length (eval xs)
--eval (ListFilter f xs) = filter_ (eval f) (eval xs)
eval (Pair a b) = ((,) $! eval a) $! eval b
eval (Fst p)    = fst (eval p)
eval (Snd p)    = snd (eval p)
eval (NumCast a) = fromIntegral (eval a)
eval (Abort reason) = throwM (AbortException reason)
eval (UpdatePrivTree node value tree) = update (eval node) (eval value) (eval tree)
