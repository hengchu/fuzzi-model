{-# OPTIONS_HADDOCK hide #-}

module Data.Fuzzi.Types (
  module Data.Fuzzi.Types.Internal
  , module Data.Fuzzi.Types.Structures
  , module Data.Fuzzi.Types.Optimize
  , module Data.Fuzzi.Types.SymbolicExpr
  , FractionalOf
  ) where

import Data.Fuzzi.Types.Internal
import Data.Fuzzi.Types.Structures
import Data.Fuzzi.Types.Optimize
import Data.Fuzzi.Types.SymbolicExpr

type family FractionalOf (t :: *) = (r :: *) | r -> t

type instance FractionalOf Integer = Double
type instance FractionalOf IntExpr = RealExpr
