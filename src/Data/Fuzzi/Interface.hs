{-# OPTIONS_HADDOCK prune #-}

{-|
Module: Data.Fuzzi.Interface
Description: The EDSL programming interafce for creating embedded programs for DP testing.
-}
module Data.Fuzzi.Interface (
  -- ** Types and classes for converting programs between their deep and shallow representations
  Fuzzi
  , Syntactic
  , Syntactic1
  , Mon

  -- ** Combinators for expressing probabilistic programs
  , if_
  , ifM
  , lap
  , geo
  , lap'
  , fst_
  , snd_
  , pair
  , lit
  , true
  , false
  , abort
  , updatePT
  , nil
  , cons
  , snoc
  , isNil
  , uncons
  , just
  , nothing
  , isJust_
  , fromJust_
  , fromIntegral_
  , reify
  , streamline
  , loop
  , gauss
  , gauss'

  , module Data.Fuzzi.Types
  ) where

import Data.Fuzzi.Types
import Data.Fuzzi.EDSL
