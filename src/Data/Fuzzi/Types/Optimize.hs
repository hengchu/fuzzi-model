module Data.Fuzzi.Types.Optimize where

import Data.Fuzzi.Types.SymbolicExpr
import Prelude hiding (and, or)
import qualified Data.Set as S

optimizeBool :: BoolExpr -> BoolExpr
optimizeBool = BoolExpr . cataTree treeOptimization . intoTree

data AndOrTree :: * where
  Ands  :: [AndOrTree] -> AndOrTree
  Ors   :: [AndOrTree] -> AndOrTree
  Other :: SymbolicExpr -> AndOrTree
  deriving (Show, Eq, Ord)

data FoldAndOrTree (r :: *) where
  Folds  :: ([r]  -> r)  -- fold Ands
         -> ([r]  -> r)  -- fold Ors
         -> (SymbolicExpr -> r) -- fold Other
         -> FoldAndOrTree r

isAnds :: AndOrTree -> Maybe [AndOrTree]
isAnds (Ands xs) = Just xs
isAnds _ = Nothing

cataTree :: FoldAndOrTree r -> AndOrTree -> r
cataTree alg@(Folds f  _ _) (Ands  ands) =
  f (fmap (cataTree alg) ands)
cataTree alg@(Folds _ f _) (Ors   ors) =
  f (fmap (cataTree alg) ors)
cataTree     (Folds _ _ f) (Other other)
  = f other

intoTree :: BoolExpr -> AndOrTree
intoTree = intoTree' . getBoolExpr

intoTree' :: SymbolicExpr -> AndOrTree
intoTree' (a `And` b) = Ands $ (fmap intoTree' (expandAnd a ++ expandAnd b))
intoTree' (a `Or` b)  = Ors  $ (fmap intoTree' (expandOr  a ++ expandOr  b))
intoTree' a           = Other a

treeOptimization :: FoldAndOrTree SymbolicExpr
treeOptimization =
  Folds (foldr1 And . S.fromList) (foldr1 Or . S.fromList) id

expandAnd :: SymbolicExpr -> [SymbolicExpr]
expandAnd (And a b) = expandAnd a ++ expandAnd b
expandAnd x         = [x]

expandOr :: SymbolicExpr -> [SymbolicExpr]
expandOr (Or a b) = expandOr a ++ expandOr b
expandOr x        = [x]
