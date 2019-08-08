module Interp (
  module Interp.StraightForward
  , module Interp.Types
  , module Interp.Tracing
  , module Interp.Concrete
  , module Interp.TracingConcrete
  , runInterpreter
  , runMultiInterpreter
  ) where

import Control.Applicative.Free (runAp)
import Interp.Concrete
import Interp.StraightForward
import Interp.Tracing
import Interp.TracingConcrete
import Interp.Types
import Term
import Data.Functor.Compose
import ListT

runInterpreter :: forall interp bool a.
                  (Interpretation interp, Decision interp ~ bool)
               => interp
               -> Fuzzi (Domain interp) bool a
               -> (Domain interp) a
runInterpreter interp = runAp (step interp)


runMultiInterpreter :: forall interp bool a.
                       (MultiInterpretation interp, MultiDecision interp ~ bool)
                    => interp
                    -> Fuzzi (MultiDomain interp) bool a
                    -> (MultiDomain interp) [a]
runMultiInterpreter interp prog = toList $ runAp (stepAll interp) prog
