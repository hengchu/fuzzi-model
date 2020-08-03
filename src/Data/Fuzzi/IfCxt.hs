{-# OPTIONS_HADDOCK hide #-}
module Data.Fuzzi.IfCxt where

import Data.Kind

-- See https://github.com/mikeizbicki/ifcxt/blob/master/src/IfCxt.hs
-- for how this magic works.

class IfCxt (cxt :: Constraint) where
  ifCxt :: proxy cxt -> (cxt => a) -> a -> a

instance {-# OVERLAPPABLE #-} IfCxt cxt where
  ifCxt _ _ f = f
