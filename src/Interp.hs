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

runInterpreter :: forall interp a. (Interpretation interp)
               => Fuzzi (Domain interp) a
               -> (Domain interp) a
runInterpreter = runAp (step @interp)


runMultiInterpreter :: forall interp a. (MultiInterpretation interp)
                    => Fuzzi (MultiDomain interp) a
                    -> [(MultiDomain interp) a]
runMultiInterpreter prog = getCompose $ runAp (stepAll @interp) prog
