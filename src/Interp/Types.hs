module Interp.Types where

import Term
import Model
import Type.Reflection

data Trace :: * -> * where
  TrLap   :: a -> Double -> Trace a
  TrGauss :: a -> Double -> Trace a
  deriving Show

data SomeTrace :: * where
  MkSomeTrace :: (Show a, Model domain a) => TypeRep domain -> Trace a -> SomeTrace

deriving instance Show SomeTrace

trLap :: forall domain a. (Typeable domain, Show a, Model domain a) => a -> Double -> SomeTrace
trLap center width = MkSomeTrace (typeRep @domain) (TrLap center width)

trGauss :: forall domain a. (Typeable domain, Show a, Model domain a) => a -> Double -> SomeTrace
trGauss center width = MkSomeTrace (typeRep @domain) (TrGauss center width)

class Applicative (Domain interpreter) => Interpretation interpreter where
  type Domain interpreter :: * -> *
  step :: FuzziF (Domain interpreter) a -> (Domain interpreter) a
