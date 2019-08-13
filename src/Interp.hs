module Interp where

import Data.Proxy
import Prelude hiding (and, or)
import IfCxt
import EDSL
import Types
import Type.Reflection hiding (App)

monadDistErrorMessage :: String
monadDistErrorMessage = "encoding MonadDist and interpretation MonadDist are different"

eval :: forall a. Fuzzi a -> a
eval (Lam f) = eval . f . Lit
eval (App f a) = (eval f) (eval a)
eval (Return a) = return (eval a)
eval (Bind a f) = (eval a) >>= (eval . f . Lit)
eval (Lit a) = a
eval (If cond t f) = if toBool (eval cond) then eval t else eval f
eval (IfM (cond :: Fuzzi bool) t f) =
  ifCxt (Proxy :: Proxy (ConcreteBoolean bool))
        (if toBool (eval cond) then eval t else eval f)
        (error ("The type "
                ++ (show $ typeRep @bool)
                ++ " does not support concrete execution"))
eval (Laplace _ c w) = laplace (eval c) w
eval (Gaussian _ c w) = gaussian (eval c) w
eval (Variable v) = error ("unexpected variable " ++ show v ++ " :: " ++ show (typeRep @a))
eval (And a b) = and (eval a) (eval b)
eval (Or a b) = or (eval a) (eval b)
eval (Not a) = neg (eval a)
eval (Add a b) = (eval a) + (eval b)
eval (Mult a b) = (eval a) * (eval b)
eval (Sub a b) = (eval a) - (eval b)
eval (Sign a) = signum (eval a)
eval (Abs a) = abs (eval a)
eval (Div a b) = (eval a) / (eval b)
eval (Lt a b) = (eval a) %< (eval b)
eval (Le a b) = (eval a) %<= (eval b)
eval (Gt a b) = (eval a) %> (eval b)
eval (Ge a b) = (eval a) %>= (eval b)
eval (Eq_ a b) = (eval a) %== (eval b)
eval (Neq a b) = (eval a) %/= (eval b)
eval (AssertTrueM cond v) = do
  assertTrue (eval cond)
  eval v
eval (AssertFalseM cond v) = do
  assertFalse (eval cond)
  eval v
