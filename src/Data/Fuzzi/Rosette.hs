module Data.Fuzzi.Rosette where

import Prelude hiding (and)
import Control.Monad
import Data.Functor.Compose
import Data.Fuzzi.EDSL
import Data.Fuzzi.Symbol
import Data.Fuzzi.Types
import Data.Fuzzi.Interp
import Control.Monad.Catch

-- TODO: Also need MonadState to keep track of concrete traces, and for
-- generating fresh symbols
evalM :: (MonadDist m, MonadAssert m, NumDomain m ~ RealExpr, BoolType m ~ BoolExpr)
      => Fuzzi (m a) -> m (GuardedSymbolicUnion a)
evalM (Return a) = return (pure $ evalPure a)
evalM (Sequence a b) = do
  ua <- evalM a
  ub <- sequence $ fmap (evalM . const b) ua
  return (joinGuardedSymbolicUnion ub)
evalM (Bind a f) = do
  ua <- evalM a
  ub <- sequence $ fmap (evalM . f . Lit) ua
  return (joinGuardedSymbolicUnion ub)
evalM (IfM cond a b) = do
  let cond' = evalPure cond
  -- TODO: push symbolic state here? laplace/gaussian will consume traces, but
  -- we can't let them diverge after the if statement
  a' <- evalM a
  b' <- evalM b
  return $ mergeUnion cond'
    (joinGuardedSymbolicUnion $ guardedSingleton cond' a')
    (joinGuardedSymbolicUnion $ guardedSingleton (neg cond') b')
evalM (Abort reason) = throwM (AbortException reason)
evalM (Laplace' tolerance center width) = do
  sample <- laplace' tolerance (evalPure center) width
  -- TODO: attach coupling constraints here instead of using pure
  return (pure sample)
evalM (Laplace center width) = do
  sample <- laplace (evalPure center) width
  -- TODO: attach coupling constraints here instead of using pure
  return (pure sample)
evalM (Gaussian' tolerance center width) = do
  sample <- gaussian' tolerance (evalPure center) width
  -- TODO: attach coupling constraints here instead of using pure
  return (pure sample)
evalM (Gaussian center width) = do
  sample <- gaussian (evalPure center) width
  -- TODO: attach coupling constraints here instead of using pure
  return (pure sample)
evalM other = error "evalM: received a non-monadic Fuzzi construct"

evalPure :: FuzziType a => Fuzzi a -> a
evalPure = eval
