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

singleton :: a -> SymbolicUnion a
singleton = Singleton

guarded :: BoolExpr -> a -> Guarded a
guarded = MkGuarded

union :: GuardedSymbolicUnion a -> GuardedSymbolicUnion a -> GuardedSymbolicUnion a
union (Compose u1) (Compose u2) = Compose $ u1 `Union` u2

flatten :: GuardedSymbolicUnion a -> [(BoolExpr, a)]
flatten (Compose u) = map (\(MkGuarded cond v) -> (cond, v)) (toList u)

fromList :: [(BoolExpr, a)] -> Maybe (GuardedSymbolicUnion a)
fromList ((cond, a):xs) = Just $ foldr (\(cond, v) acc -> (guardedSingleton cond v) `union` acc) (guardedSingleton cond a) xs
fromList []             = Nothing

diff :: Eq a => GuardedSymbolicUnion a -> GuardedSymbolicUnion a -> Maybe (GuardedSymbolicUnion a)
diff ua ub = fromList $ flatten ua \\ flatten ub

same :: Eq a => GuardedSymbolicUnion a -> GuardedSymbolicUnion a -> Bool
same ua ub = isNothing (diff ua ub) && isNothing (diff ub ua)

flattenMaybe :: Maybe (GuardedSymbolicUnion a) -> [(BoolExpr, a)]
flattenMaybe Nothing = []
flattenMaybe (Just u) = flatten u

guardedSingleton :: BoolExpr -> a -> GuardedSymbolicUnion a
guardedSingleton cond = Compose . singleton . guarded cond

conjunct :: BoolExpr -> Guarded a -> Guarded a
conjunct cond (MkGuarded cond2 a) = MkGuarded (cond `and` cond2) a

disjunct :: BoolExpr -> Guarded a -> Guarded a
disjunct cond (MkGuarded cond2 a) = MkGuarded (cond `or` cond2) a

conjunctAll :: BoolExpr -> GuardedSymbolicUnion a -> GuardedSymbolicUnion a
conjunctAll cond union = Compose $ fmap (conjunct cond) (getCompose union)

disjunctAll :: BoolExpr -> GuardedSymbolicUnion a -> GuardedSymbolicUnion a
disjunctAll cond union = Compose $ fmap (disjunct cond) (getCompose union)

isFreeSingleton :: GuardedSymbolicUnion a -> Maybe a
isFreeSingleton (Compose (Singleton (MkGuarded (tryEvalBool -> Just True) a))) = Just a
isFreeSingleton _ = Nothing

isSingleton' :: GuardedSymbolicUnion a -> Maybe (Guarded a)
isSingleton' (Compose (Singleton a)) = Just a
isSingleton' _                       = Nothing

isSingleton :: GuardedSymbolicUnion a -> Bool
isSingleton = isJust . isSingleton'

isUnion :: GuardedSymbolicUnion a -> Bool
isUnion = not . isSingleton

filterGuardedSymbolicUnion :: (a -> Bool) -> GuardedSymbolicUnion a -> Maybe (GuardedSymbolicUnion a)
filterGuardedSymbolicUnion p (Compose (Singleton ga@(MkGuarded _ a)))
  | p a       = Just (Compose (Singleton ga))
  | otherwise = Nothing
filterGuardedSymbolicUnion p (Compose (Union u1 u2)) =
  case (filterGuardedSymbolicUnion p (Compose u1), filterGuardedSymbolicUnion p (Compose u2)) of
    (Just (Compose u1'), Just (Compose u2')) -> Just (Compose $ u1' `Union` u2')
    (Just (Compose u1'), _                 ) -> Just (Compose u1')
    (_                 , Just (Compose u2')) -> Just (Compose u2')
    _                                        -> Nothing

-- |Here, we find a maximum matching between the two sets of symbolic
-- unions. The first item in the triple is the matched core, the second is the
-- leftover from left union, and the third is leftover from right union.
symmetricDiff :: (SymbolicRepr a, Ord a)
              => GuardedSymbolicUnion a
              -> GuardedSymbolicUnion a
              -> ( [(BoolExpr, BoolExpr, a, a)]
                 , Maybe (GuardedSymbolicUnion a)
                 , Maybe (GuardedSymbolicUnion a)
                 )
symmetricDiff left right =
  let edges =
        S.fromList [ ((condA, a), (condB, b))
                   | (condA, a) <- flatten left
                   , (condB, b) <- flatten right
                   , match a b]
      core  = map (\((condA, a), (condB, b)) -> (condA, condB, a, b)) $ M.toList (matching edges)
      elems = nub $ map (view _3) core ++ map (view _4) core
      leftOver  = filterGuardedSymbolicUnion (\v -> not $ v `elem` elems) left
      rightOver = filterGuardedSymbolicUnion (\v -> not $ v `elem` elems) right
  in (core, leftOver, rightOver)

-- |Merge two guarded symbolic unions. This is the mu function in the Rosette
-- paper.
mergeUnion :: ( SymbolicRepr a
              , Ord a
              )
           => BoolExpr
           -> GuardedSymbolicUnion a
           -> GuardedSymbolicUnion a
           -> GuardedSymbolicUnion a
mergeUnion (tryEvalBool -> Just True)  left _right = left
mergeUnion (tryEvalBool -> Just False) _left right = right
mergeUnion _                           left right | getCompose left == getCompose right = left
mergeUnion cond (isFreeSingleton -> Just left) (isFreeSingleton -> Just right) = merge cond left right
mergeUnion cond left (isFreeSingleton -> Just right) =
  case filterGuardedSymbolicUnion (`match` right) left of
    Nothing   -> (conjunctAll cond left) `union` (guardedSingleton (neg cond) right)
    Just core ->
      case left `diff` core of
        Nothing ->
          foldr1 union
            $ fmap (\(condU, u) ->
                      conjunctAll
                        (neg cond `or` condU) -- cond ==> condU
                          $ merge cond u right)
                   (flatten left)
        Just complement ->
          foldr union (conjunctAll cond complement)
            $ fmap (\(condU, u) ->
                      conjunctAll
                        (neg cond `or` condU) -- cond ==> condU
                          $ merge cond u right)
                   (flatten left)
mergeUnion cond (isFreeSingleton -> Just left) right = mergeUnion (neg cond) right (pure left)
mergeUnion cond left right =
  let (w, u, v) = symmetricDiff left right
      mkW = \(bi, bj, ui, vj) ->
        let cond' = (cond `and` bi) `or` ((neg cond) `and` bj)
        in getCompose $ conjunctAll cond' (mergeUnion cond (pure ui) (pure vj))
      subWUnions = map mkW w
  in case (subWUnions, u, v) of
       (x:xs, Just u', Just v') ->
         (Compose (foldl' Union x xs))
         `union` (conjunctAll cond u')
         `union` (conjunctAll (neg cond) v')
       (x:xs, Just u', Nothing) ->
         (Compose (foldl' Union x xs))
         `union` (conjunctAll cond u')
       (x:xs, Nothing, Just v') ->
         (Compose (foldl' Union x xs))
         `union` (conjunctAll (neg cond) v')
       (x:xs, Nothing, Nothing) ->
         Compose $ (foldl' Union x xs)
       ([], Just left', Just right') ->
         left' `union` right'
       ([], _,          _) ->
         error "mergeUnion: the impossible happened, symmetricDiff lost some data"


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
    in pure $ RealExpr tol' (Ite (getBoolExpr cond) (getRealExpr left) (getRealExpr right))

instance SymbolicRepr BoolExpr where
  merge cond left right =
    pure $ BoolExpr (Ite (getBoolExpr cond) (getBoolExpr left) (getBoolExpr right))

instance SymbolicRepr IntExpr where
  merge cond left right =
    pure $ IntExpr (Ite (getBoolExpr cond) (getIntExpr left) (getIntExpr right))

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
      in case sequenceA (map isFreeSingleton unions) of
           Just singletonList -> pure singletonList
           Nothing -> guardedSingleton cond lefts `union` guardedSingleton (neg cond) rights
    | otherwise = guardedSingleton cond lefts `union` guardedSingleton (neg cond) rights

instance SymbolicRepr a => SymbolicRepr (Maybe a) where
  merge = undefined

instance (SymbolicRepr a, SymbolicRepr b) => SymbolicRepr (a, b) where
  merge = undefined

instance Applicative Guarded where
  pure = guarded (bool True)
  (MkGuarded cond1 f) <*> (MkGuarded cond2 a) =
    MkGuarded (cond1 `and` cond2) (f a)

instance Applicative SymbolicUnion where
  pure = Singleton
  (Singleton f)   <*> (Singleton a)   = Singleton (f a)
  (Singleton f)   <*> (u1 `Union` u2) = (fmap f u1) `Union` (fmap f u2)
  (f1 `Union` f2) <*> (Singleton a)   = (fmap ($ a) f1) `Union` (fmap ($ a) f2)
  (f1 `Union` f2) <*> (u1 `Union` u2) =
    (f1 <*> u1) `Union` (f1 <*> u2) `Union` (f2 <*> u1) `Union` (f2 <*> u2)

instance Monad GuardedSymbolicUnion where
  return = pure
  a >>= f =
    let uub = fmap f a
    in joinGuardedSymbolicUnion uub

joinGuardedSymbolicUnion :: GuardedSymbolicUnion (GuardedSymbolicUnion a) -> GuardedSymbolicUnion a
joinGuardedSymbolicUnion (Compose (Singleton (MkGuarded conds union))) = conjunctAll conds union
joinGuardedSymbolicUnion (Compose (Union u1 u2)) =
  let j1 = getCompose $ joinGuardedSymbolicUnion (Compose u1)
      j2 = getCompose $ joinGuardedSymbolicUnion (Compose u2)
  in Compose $ Union j1 j2

-- this is just to make ghci happy to show Compose f g
$(deriveShow1 ''SymbolicUnion)
$(deriveShow1 ''Guarded)
