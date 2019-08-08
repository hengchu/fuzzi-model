module Interp.Concrete where

import Distribution (Dist)
import Distribution as D
import Interp.Types
import Term
import qualified Model as M

type ConcreteDomain = Dist

concreteInterp :: FuzziF ConcreteDomain Bool a -> ConcreteDomain a
concreteInterp (FPure x) = pure x
concreteInterp (FAp f a) =
  concreteInterp f <*> concreteInterp a
concreteInterp (FWithSample a f) = do
  a' <- concreteInterp a
  concreteInterp $ f a'
concreteInterp (FLaplace center width) = do
  center' <- concreteInterp center
  M.laplace center' width
concreteInterp (FGaussian center width) = do
  center' <- concreteInterp center
  M.gaussian center' width
concreteInterp (FIf cond truecmd falsecmd) = do
  cond' <- concreteInterp cond
  if cond'
  then concreteInterp truecmd
  else concreteInterp falsecmd

data ConcreteInterp

instance Interpretation ConcreteInterp where
  type Domain ConcreteInterp = ConcreteDomain
  type Decision ConcreteInterp = Bool
  step = concreteInterp
