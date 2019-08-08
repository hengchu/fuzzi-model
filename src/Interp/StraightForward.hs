module Interp.StraightForward where

import Interp.Types
import Term
import Data.Functor.Identity
import qualified Model as M

straightforwardInterp :: FuzziF M.NoRandomness Bool a -> M.NoRandomness a
straightforwardInterp (FPure a) =
  M.NoRandomness a
straightforwardInterp (FAp f a) =
  M.NoRandomness
  $ (M.unwrapNoRandomness (straightforwardInterp f))
    (M.unwrapNoRandomness (straightforwardInterp a))
straightforwardInterp (FLaplace center width) =
  M.laplace (M.unwrapNoRandomness $ straightforwardInterp center) width
straightforwardInterp (FGaussian center width) =
  M.gaussian (M.unwrapNoRandomness $ straightforwardInterp center) width
straightforwardInterp (FIf cond truecmd falsecmd) =
  if M.unwrapNoRandomness $ straightforwardInterp cond
  then straightforwardInterp truecmd
  else straightforwardInterp falsecmd
straightforwardInterp (FWithSample a f) =
  straightforwardInterp $ f (M.unwrapNoRandomness $ straightforwardInterp a)

data StraightForwardInterp = StraightForwardInterp

instance Interpretation StraightForwardInterp where
  type Domain StraightForwardInterp = M.NoRandomness
  type Decision StraightForwardInterp = Bool
  step _ = straightforwardInterp
