module Data.Fuzzi.Types.Optimize where

import Data.Fuzzi.Types.SymbolicExpr
import Prelude hiding (and, or)
import qualified Data.Set as S
import Data.Graph.MaxBipartiteMatching
import qualified Data.Map.Strict as M

optimizeBool :: BoolExpr -> BoolExpr
optimizeBool = BoolExpr . cataTree treeOptimization . intoTree

data AndOrTree :: * where
  Ands  :: [AndOrTree] -> AndOrTree
  Ors   :: [AndOrTree] -> AndOrTree
  Other :: SymbolicExpr -> AndOrTree
  deriving (Show, Eq, Ord)

data FoldAndOrTree (r :: *) where
  Folds  :: ([r]  -> r)  -- fold Ands
         -> ([[r]] -> [r]) -- fold Ors [And ..., And ..., And ...]
         -> ([r]  -> r)  -- fold Ors
         -> (SymbolicExpr -> r) -- fold Other
         -> FoldAndOrTree r

isAnds :: AndOrTree -> Maybe [AndOrTree]
isAnds (Ands xs) = Just xs
isAnds _ = Nothing

cataTree :: FoldAndOrTree r -> AndOrTree -> r
cataTree alg@(Folds f _ _ _) (Ands  ands) =
  f (fmap (cataTree alg) ands)
--cataTree alg@(Folds _ f _ _) (Ors (traverse isAnds -> Just ands)) =
--  f (fmap (fmap (cataTree alg)) ands)
cataTree alg@(Folds _ _ f _) (Ors   ors) =
  f (fmap (cataTree alg) ors)
cataTree     (Folds _ _ _ f) (Other other)
  = f other

intoTree :: BoolExpr -> AndOrTree
intoTree = intoTree' . getBoolExpr

intoTree' :: SymbolicExpr -> AndOrTree
intoTree' (a `And` b) = Ands $ (fmap intoTree' (S.toList $ expandAnd a `S.union` expandAnd b))
intoTree' (a `Or` b)  = Ors  $ (fmap intoTree' (S.toList $ expandOr  a `S.union` expandOr  b))
intoTree' a           = Other a

treeOptimization :: FoldAndOrTree SymbolicExpr
treeOptimization =
  Folds (foldr1 And) undefined (foldr1 Or) id

{-
irrelevantCondReductionStep :: [SymbolicExpr] -> [SymbolicExpr] -> [SymbolicExpr]
irrelevantCondReductionStep lefts rights =
  let edges = S.fromList [(l, r) | l <- lefts, r <- rights, l == Not r || Not l == r]
      core  = M.toList $ matching edges
      lefts' = (S.fromList lefts) S.\\ (S.fromList $ map snd core)
      rights' = (S.fromList rights) S.\\ (S.fromList $ map fst core)
  in [foldr1 And lefts', foldr1 And rights']

irrelevantCondReduction :: [[SymbolicExpr]] -> SymbolicExpr
irrelevantCondReduction []                 = error "impossible case"
irrelevantCondReduction [cond]             = foldr1 And cond
irrelevantCondReduction (ands1:ands2:more) =
   foldr Or (irrelevantCondReductionStep ands1 ands2) (map (foldr1 And) more)
-}

expandAnd :: SymbolicExpr -> S.Set SymbolicExpr
expandAnd (And a b) = S.union (expandAnd a) (expandAnd b)
expandAnd x         = S.singleton x

expandOr :: SymbolicExpr -> S.Set SymbolicExpr
expandOr (Or a b) = S.union (expandOr a) (expandOr b)
expandOr x        = S.singleton x
