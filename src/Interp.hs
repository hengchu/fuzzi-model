module Interp (
  module Interp.StraightForward
  , module Interp.Types
  , module Interp.Tracing
  , module Interp.Concrete
  , module Interp.TracingConcrete
  , runInterpreter
  ) where

import Control.Applicative.Free (runAp)
import Interp.Concrete
import Interp.StraightForward
import Interp.Tracing
import Interp.TracingConcrete
import Interp.Types
import Term

runInterpreter :: forall interp a. (Interpretation interp)
               => Fuzzi (Domain interp) a
               -> (Domain interp) a
runInterpreter = runAp (step @interp)
