module Data.Fuzzi.Types.Structures where

import Control.Lens hiding (matching)
import Data.Foldable hiding (and, or)
import Data.Functor.Compose
import Data.Fuzzi.Types.Internal
import Data.Graph.MaxBipartiteMatching
import Data.List (nub, (\\))
import Data.Maybe (isNothing, isJust)
import Prelude hiding (and, or)
import Text.Show.Deriving (deriveShow1)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

wrap :: [Guarded a] -> GuardedSymbolicUnion a
wrap = GuardedSymbolicUnion

unwrap :: GuardedSymbolicUnion a -> [Guarded a]
unwrap = unwrapGuardedSymbolicUnion

reduce :: SymbolicRepr a => GuardedSymbolicUnion a -> GuardedSymbolicUnion a
reduce (unwrap -> u) = wrap . S.toList . S.fromList $ u

guarded :: BoolExpr -> a -> Guarded a
guarded = MkGuarded

union :: GuardedSymbolicUnion a -> GuardedSymbolicUnion a -> GuardedSymbolicUnion a
union (unwrap -> u1) (unwrap -> u2) = wrap $ u1 ++ u2

flatten :: GuardedSymbolicUnion a -> [(BoolExpr, a)]
flatten (unwrap -> u) = map (\(MkGuarded cond v) -> (cond, v)) u

fromList :: [(BoolExpr, a)] -> GuardedSymbolicUnion a
fromList = foldr (\(cond, v) acc -> guardedSingleton cond v `union` acc) (wrap [])

diff :: SymbolicRepr a => GuardedSymbolicUnion a -> GuardedSymbolicUnion a -> GuardedSymbolicUnion a
diff ua ub = fromList . S.toList $ S.fromList (flatten ua) S.\\ S.fromList (flatten ub)

same :: SymbolicRepr a => GuardedSymbolicUnion a -> GuardedSymbolicUnion a -> Bool
same ua ub = null (diff ua ub) && null (diff ub ua)

guardedSingleton :: BoolExpr -> a -> GuardedSymbolicUnion a
guardedSingleton cond = wrap . (:[]) . guarded cond

conjunct :: BoolExpr -> Guarded a -> Guarded a
conjunct cond (MkGuarded cond2 a) = MkGuarded (cond `and` cond2) a

disjunct :: BoolExpr -> Guarded a -> Guarded a
disjunct cond (MkGuarded cond2 a) = MkGuarded (cond `or` cond2) a

conjunctAll :: BoolExpr -> GuardedSymbolicUnion a -> GuardedSymbolicUnion a
conjunctAll cond (unwrap -> union) = wrap $ fmap (conjunct cond) union

disjunctAll :: BoolExpr -> GuardedSymbolicUnion a -> GuardedSymbolicUnion a
disjunctAll cond (unwrap -> union) = wrap $ fmap (disjunct cond) union

isFreeSingleton :: GuardedSymbolicUnion a -> Maybe a
isFreeSingleton (unwrap -> [MkGuarded (tryEvalBool -> Just True) a]) = Just a
isFreeSingleton _ = Nothing

filterGuardedSymbolicUnion :: (a -> Bool) -> GuardedSymbolicUnion a -> GuardedSymbolicUnion a
filterGuardedSymbolicUnion p (unwrap -> u) = wrap $ filter (\(MkGuarded _ v) -> p v) u

-- |Here, we find a maximum matching between the two sets of symbolic
-- unions. The first item in the triple is the matched core, the second is the
-- leftover from left union, and the third is leftover from right union.
symmetricDiff :: SymbolicRepr a
              => GuardedSymbolicUnion a
              -> GuardedSymbolicUnion a
              -> ( [(BoolExpr, BoolExpr, a, a)]
                 , GuardedSymbolicUnion a
                 , GuardedSymbolicUnion a
                 )
symmetricDiff left right =
  let edges =
        S.fromList [ ((condA, a), (condB, b))
                   | (condA, a) <- flatten left
                   , (condB, b) <- flatten right
                   , match a b]
      core  = map (\((condA, a), (condB, b)) -> (condA, condB, a, b)) $ M.toList (matching edges)
      elems = nub $ map (view _3) core ++ map (view _4) core
      leftOver  = filterGuardedSymbolicUnion (`notElem` elems) left
      rightOver = filterGuardedSymbolicUnion (`notElem` elems) right
  in (core, leftOver, rightOver)

-- |Merge two guarded symbolic unions. This is the mu function in the Rosette
-- paper.
mergeUnion :: SymbolicRepr a
           => BoolExpr
           -> GuardedSymbolicUnion a
           -> GuardedSymbolicUnion a
           -> GuardedSymbolicUnion a
mergeUnion cond a b = reduce $ mergeUnion' cond a b

mergeUnion' :: SymbolicRepr a
            => BoolExpr
            -> GuardedSymbolicUnion a
            -> GuardedSymbolicUnion a
            -> GuardedSymbolicUnion a
mergeUnion' (tryEvalBool -> Just True)  left _right = left
mergeUnion' (tryEvalBool -> Just False) _left right = right
mergeUnion' _                           left right | left == right = left
mergeUnion' cond (isFreeSingleton -> Just left) (isFreeSingleton -> Just right) = merge cond left right
mergeUnion' cond left (isFreeSingleton -> Just right) =
  case filterGuardedSymbolicUnion (`match` right) left of
    core ->
      case left `diff` core of
        complement ->
          foldr union (conjunctAll cond complement)
            $ fmap (\(condU, u) ->
                      conjunctAll
                        (neg cond `or` condU) -- cond ==> condU
                          $ merge cond u right)
                   (flatten left)
mergeUnion' cond (isFreeSingleton -> Just left) right = mergeUnion (neg cond) right (pure left)
mergeUnion' cond left right =
  let (w, u, v) = symmetricDiff left right
      mkW (bi, bj, ui, vj) =
        let cond' = (cond `and` bi) `or` ((neg cond) `and` bj)
        in conjunctAll cond' (mergeUnion cond (pure ui) (pure vj))
      subWUnions = map mkW w
      init = conjunctAll cond u `union` conjunctAll (neg cond) v
  in foldr union init subWUnions

instance SymbolicRepr Int where
  merge cond left right
    | left == right = pure left
    | otherwise     = guardedSingleton cond left `union` guardedSingleton (neg cond) right

instance SymbolicRepr Double where
  merge cond left right
    | left == right = pure left
    | otherwise     = guardedSingleton cond left `union` guardedSingleton (neg cond) right

instance SymbolicRepr Bool where
  merge cond left right
    | left == right = pure left
    | otherwise     = guardedSingleton cond left `union` guardedSingleton (neg cond) right

instance SymbolicRepr RealExpr where
  merge cond left right =
    let tol' = max (getTolerance left) (getTolerance right)
    in pure $ RealExpr tol' (ite' (getBoolExpr cond) (getRealExpr left) (getRealExpr right))

instance SymbolicRepr BoolExpr where
  merge cond left right =
    pure $ BoolExpr (ite' (getBoolExpr cond) (getBoolExpr left) (getBoolExpr right))

instance SymbolicRepr IntExpr where
  merge cond left right =
    pure $ IntExpr (ite' (getBoolExpr cond) (getIntExpr left) (getIntExpr right))

instance Numeric     RealExpr
instance FracNumeric RealExpr
instance FuzziType   RealExpr
instance FuzziType   BoolExpr
instance FuzziType   IntExpr

instance FuzziType Double
instance FuzziType Bool
instance FuzziType Int
instance FuzziType a => FuzziType (PrivTree1D a)
instance FuzziType a => FuzziType [a]
instance FuzziType a => FuzziType (Maybe a)
instance FuzziType PrivTreeNode1D
instance (FuzziType a, FuzziType b) => FuzziType (a, b)

instance SymbolicRepr PrivTreeNode1D where
  merge cond left right
    | left == right = pure left
    | otherwise     = guardedSingleton cond left `union` guardedSingleton (neg cond) right

instance SymbolicRepr a => SymbolicRepr (PrivTree1D a) where
  merge = undefined

instance SymbolicRepr a => SymbolicRepr [a] where
  merge cond lefts rights
    | length lefts == length rights =
      let unions = zipWith (merge cond) lefts rights
      in case traverse isFreeSingleton unions of
           Just singletonList -> pure singletonList
           Nothing -> guardedSingleton cond lefts `union` guardedSingleton (neg cond) rights
    | otherwise = guardedSingleton cond lefts `union` guardedSingleton (neg cond) rights

instance SymbolicRepr a => SymbolicRepr (Maybe a) where
  merge = undefined

instance (SymbolicRepr a, SymbolicRepr b) => SymbolicRepr (a, b) where
  merge = undefined

instance Monad GuardedSymbolicUnion where
  return = pure
  a >>= f =
    let uub = fmap f a
    in joinGuardedSymbolicUnion uub

joinGuardedSymbolicUnion :: GuardedSymbolicUnion (GuardedSymbolicUnion a) -> GuardedSymbolicUnion a
joinGuardedSymbolicUnion (unwrap -> []) = wrap []
joinGuardedSymbolicUnion (unwrap -> (MkGuarded conds u):guardedUnions) =
  conjunctAll conds u `union` joinGuardedSymbolicUnion (wrap guardedUnions)
