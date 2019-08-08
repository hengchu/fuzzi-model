module Interp.TracingConcrete where

import Control.Monad.Writer.Strict
import Distribution (Dist)
import Interp.Types
import Term
import qualified Model as M

type TracingConcreteDomain = WriterT [SomeTrace] Dist

tracingConcreteInterp :: FuzziF TracingConcreteDomain Bool a -> TracingConcreteDomain a
tracingConcreteInterp (FPure x) = pure x
tracingConcreteInterp (FAp f a) =
  tracingConcreteInterp f <*> tracingConcreteInterp a
tracingConcreteInterp (FLaplace center width) = do
  center' <- tracingConcreteInterp center
  tell [trLap @TracingConcreteDomain center' width]
  M.laplace center' width
tracingConcreteInterp (FGaussian center width) = do
  center' <- tracingConcreteInterp center
  tell [trGauss @TracingConcreteDomain center' width]
  M.gaussian center' width
tracingConcreteInterp (FWithSample a f) = do
  a' <- tracingConcreteInterp a
  tracingConcreteInterp $ f a'
tracingConcreteInterp (FIf cond truecmd falsecmd) = do
  cond' <- tracingConcreteInterp cond
  if cond'
  then tracingConcreteInterp truecmd
  else tracingConcreteInterp falsecmd

data TracingConcreteInterp

instance Interpretation TracingConcreteInterp where
  type Domain TracingConcreteInterp = TracingConcreteDomain
  type Decision TracingConcreteInterp = Bool
  step = tracingConcreteInterp
