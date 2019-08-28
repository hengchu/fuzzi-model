module Data.Fuzzi.NeighborGen (
  Neighbor(..)
  , PairWiseL1List
  , pairWiseL1
  , shrinkPairWiseL1
  , L1List
  , l1List
  , shrinkL1List
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

makeLensesWith abbreviatedFields ''PairWiseL1List
makeLensesWith abbreviatedFields ''L1List

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
