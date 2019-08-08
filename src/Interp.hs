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

runInterpreter :: forall interp bool a.
                  (Interpretation interp, Decision interp ~ bool)
               => Fuzzi (Domain interp) bool a
               -> (Domain interp) a
runInterpreter = runAp (step @interp)


runMultiInterpreter :: forall interp bool a.
                       (MultiInterpretation interp, MultiDecision interp ~ bool)
                    => Fuzzi (MultiDomain interp) bool a
                    -> [(MultiDomain interp) a]
runMultiInterpreter prog = getCompose $ runAp (stepAll @interp) prog
