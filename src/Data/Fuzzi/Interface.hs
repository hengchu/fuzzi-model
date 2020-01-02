module Data.Fuzzi.Interface (
  Fuzzi
  , Syntactic
  , Syntactic1
  , Mon

  , if_
  , ifM
  , lap
  , geo
  , gauss
  , lap'
  , gauss'
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
--  , length_
  , just
  , nothing
  , fromIntegral_
  , reify
  , streamline

  , module Data.Fuzzi.Types
  ) where

import Data.Fuzzi.Types
import Data.Fuzzi.EDSL
