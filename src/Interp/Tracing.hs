module Interp.Tracing where

import Control.Monad.Writer.Strict
import Data.Proxy
import Interp.Types
import Term
import qualified Model as M
import Data.Functor.Identity
import Control.Monad.Cont

type TracingDomain = WriterT [SomeTrace] M.NoRandomness

tracingInterp :: FuzziF TracingDomain a -> TracingDomain a
tracingInterp (FPure x) =
  pure x
tracingInterp (FAp f a) =
  (tracingInterp f) <*> (tracingInterp a)
tracingInterp (FWithSample a f) = do
  a' <- tracingInterp a
  tracingInterp $ f a'
tracingInterp (FLaplace center width) = do
  center' <- tracingInterp center
  tell [trLap @TracingDomain center' width]
  M.laplace center' width
tracingInterp (FGaussian center width) = do
  center' <- tracingInterp center
  tell [trLap @TracingDomain center' width]
  M.gaussian center' width
tracingInterp (FIf cond truecmd falsecmd) = do
  cond' <- tracingInterp cond
  if cond'
  then tracingInterp truecmd
  else tracingInterp falsecmd

data TracingInterp

instance Interpretation TracingInterp where
  type Domain TracingInterp = TracingDomain
  step = tracingInterp
