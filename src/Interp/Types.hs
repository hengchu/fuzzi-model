module Interp.Types where

import Control.Monad.Trans.Class
import Data.Functor.Compose
import ListT
import Model
import Term
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

class Monad (Domain interpreter) => Interpretation interpreter where
  type Domain interpreter :: * -> *
  type Decision interpreter :: *
  step :: interpreter
       -> FuzziF (Domain interpreter) (Decision interpreter) a
       -> (Domain interpreter) a

class Monad (MultiDomain interpreter) => MultiInterpretation interpreter where
  type MultiDomain interpreter :: * -> *
  type MultiDecision interpreter :: *
  stepAll :: interpreter
          -> FuzziF (MultiDomain interpreter) (MultiDecision interpreter) a
          -> ListT (MultiDomain interpreter) a
