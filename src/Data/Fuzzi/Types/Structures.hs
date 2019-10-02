module Data.Fuzzi.Types.Structures where

import Control.Applicative
import Control.Lens hiding (matching)
import Data.Bifunctor
import Data.Foldable hiding (and, or)
import Data.Fuzzi.Types.Internal
import Data.Fuzzi.Types.SymbolicExpr
import Data.Fuzzi.Types.Optimize
import Data.Graph.MaxBipartiteMatching
import Data.List (nub)
import Prelude hiding (and, or)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

wrap :: [Guarded a] -> GuardedSymbolicUnion a
wrap = GuardedSymbolicUnion

unwrap :: GuardedSymbolicUnion a -> [Guarded a]
unwrap = unwrapGuardedSymbolicUnion

reduce :: SymbolicRepr a => GuardedSymbolicUnion a -> GuardedSymbolicUnion a
reduce (unwrap -> u) = fromList . map (first optimizeBool) . flatten . wrap . S.toList . S.fromList $ u

guarded :: BoolExpr -> a -> Guarded a
guarded = MkGuarded

singleton :: Guarded a -> GuardedSymbolicUnion a
singleton (MkGuarded cond a) = fromList [(cond, a)]

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
conjunct cond (MkGuarded cond2 a) = MkGuarded (cond2 `and` cond) a

disjunct :: BoolExpr -> Guarded a -> Guarded a
disjunct cond (MkGuarded cond2 a) = MkGuarded (cond2 `or` cond) a

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
                   , reduceable a b]
      core  = map (\((condB, b), (condA, a)) -> (condA, condB, a, b)) $ M.toList (matching edges)
      elems3 = nub $ map (view _3) core
      elems4 = nub $ map (view _4) core
      leftOver  = filterGuardedSymbolicUnion (`notElem` elems3) left
      rightOver = filterGuardedSymbolicUnion (`notElem` elems4) right
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
  case filterGuardedSymbolicUnion (`reduceable` right) left of
    core ->
      case left `diff` core of
        complement ->
          foldr union (conjunctAll cond complement)
            $ fmap (\(condU, u) ->
                      conjunctAll
                        (cond `imply` condU) -- cond ==> condU
                          $ merge cond u right)
                   (flatten core)
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
  reduceable left right = left == right
  merge cond left right
    | left == right = pure left
    | otherwise     = guardedSingleton cond left `union` guardedSingleton (neg cond) right

instance SymbolicRepr Double where
  reduceable left right = left == right
  merge cond left right
    | left == right = pure left
    | otherwise     = guardedSingleton cond left `union` guardedSingleton (neg cond) right

instance SymbolicRepr Bool where
  reduceable left right = left == right
  merge cond left right
    | left == right = pure left
    | otherwise     = guardedSingleton cond left `union` guardedSingleton (neg cond) right

instance SymbolicRepr RealExpr where
  reduceable _    _     = True
  merge cond left right =
    let tol' = max (getTolerance left) (getTolerance right)
    in pure $ RealExpr tol' (ite' (getBoolExpr cond) (getRealExpr left) (getRealExpr right))

instance SymbolicRepr BoolExpr where
  reduceable _    _     = True
  merge cond left right =
    pure $ BoolExpr (ite' (getBoolExpr cond) (getBoolExpr left) (getBoolExpr right))

instance SymbolicRepr IntExpr where
  reduceable _    _     = True
  merge cond left right =
    pure $ IntExpr (ite' (getBoolExpr cond) (getIntExpr left) (getIntExpr right))

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
joinGuardedSymbolicUnion _ = error "joinGuardedSymbolicUnion: dead code"

joinGuarded :: Guarded (Guarded a) -> Guarded a
joinGuarded (MkGuarded cond1 (MkGuarded cond2 a)) =
  MkGuarded (cond1 `and` cond2) a

instance Boolean a => Boolean (Guarded a) where
  and = liftA2 and
  or  = liftA2 or
  neg = fmap neg

instance Ordered a => Ordered (Guarded a) where
  type CmpResult (Guarded a) = Guarded (CmpResult a)
  (%<)  = liftA2 (%<)
  (%<=) = liftA2 (%<=)
  (%>)  = liftA2 (%>)
  (%>=) = liftA2 (%>=)
  (%==) = liftA2 (%==)
  (%/=) = liftA2 (%/=)

instance Num a => Num (Guarded a) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger = MkGuarded (bool True) . fromInteger

instance Fractional a => Fractional (Guarded a) where
  (/) = liftA2 (/)
  fromRational = MkGuarded (bool True) . fromRational

instance Numeric a => Numeric (Guarded a)
instance FracNumeric a => FracNumeric (Guarded a)
