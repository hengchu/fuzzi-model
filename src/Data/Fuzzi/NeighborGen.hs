module Data.Fuzzi.NeighborGen (
  Neighbor(..)
  , PairWiseL1List
  , pairWiseL1
  , shrinkPairWiseL1
  , L1List
  , l1List
  , shrinkL1List
  , BagList
  , bagList
  ) where

import Control.Lens
import Test.QuickCheck
import System.Random
import Control.Monad

class Neighbor a where
  type Element a :: *

  left  :: a -> Element a
  right :: a -> Element a

data PairWiseL1List a = PairWiseL1List {
  _pwlDataAndDiff :: [(a, a)]
  , _pwlDiff      :: a
  } deriving (Show, Eq, Ord)

data L1List a = L1List {
  _llListData :: [(a, a)]
  , _llDiff :: a
  } deriving (Show, Eq, Ord)

data BagList a = BagList {
  _blDataLeft :: [a]
  , _blDataRight :: [a]
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''PairWiseL1List
makeLensesWith abbreviatedFields ''L1List
makeLensesWith abbreviatedFields ''BagList

pairWiseL1 :: forall a.
              ( Fractional a
              , Random a
              )
           => a
           -> Gen (PairWiseL1List a)
pairWiseL1 diff = do
  len <- choose (3, 7)
  xs <- replicateM len (choose (-1.0, 1.0))
  ds <- replicateM len (choose (-diff, diff))
  return (PairWiseL1List (zip xs ds) diff)

shrinkPairWiseL1 :: PairWiseL1List a -> [PairWiseL1List a]
shrinkPairWiseL1 (PairWiseL1List xs diff) =
  filter (not . null . view dataAndDiff) $
    PairWiseL1List <$> shrinkList (:[]) xs <*> pure diff

l1List :: forall a.
          ( Fractional a
          , Random a
          , Ord a
          )
       => a
       -> Gen (L1List a)
l1List diff = do
  len <- choose (3, 7)
  xs1 <- replicateM len (choose (0.0, 1.0))
  xs2 <- replicateM len (choose (0.0, 1.0))
  let totalDiff = sum (zipWith (\x y -> abs (x - y)) xs1 xs2)
  if totalDiff <= diff
  then return (L1List (zip xs1 xs2) diff)
  else let reduce = map (/ (totalDiff / diff)) in
       return (L1List (zip (reduce xs1) (reduce xs2)) diff)

shrinkL1List :: L1List a -> [L1List a]
shrinkL1List (L1List xs diff) =
  filter (not . null . view listData) $
    L1List <$> shrinkList (:[]) xs <*> pure diff

bagList :: forall a. (Random a) => (a, a) -> Int -> Gen (BagList a)
bagList (lower, upper) nDiff = do
  len <- choose (3,4)
  xs1 <- replicateM len   (choose (lower, upper))
  xs2 <- replicateM nDiff (choose (lower, upper))
  xs2' <- randomlyIntersperse xs1 xs2
  return (BagList xs1 xs2')
  where randomlyIntersperse xs1      []       = return xs1
        randomlyIntersperse []       xs2      = return xs2
        randomlyIntersperse (x1:xs1) (x2:xs2) = do
          coin <- frequency [(1, pure True), (1, pure False)]
          if coin
          then randomlyIntersperse (x2:x1:xs1) xs2
          else randomlyIntersperse (x1:x2:xs1) xs2

instance (Num a) => Neighbor (PairWiseL1List a) where
  type Element (PairWiseL1List a) = [a]
  left  = map fst . view dataAndDiff
  right = map (uncurry (+)) . view dataAndDiff

instance Foldable PairWiseL1List where
  foldMap f xs = foldMap f (map fst $ xs ^. dataAndDiff)

instance Neighbor (L1List a) where
  type Element (L1List a) = [a]
  left  = map fst . view listData
  right = map snd . view listData

instance Foldable L1List where
  foldMap f xs = foldMap f (map fst $ xs ^. listData)

instance Neighbor (BagList a) where
  type Element (BagList a) = [a]
  left  = view dataLeft
  right = view dataRight
