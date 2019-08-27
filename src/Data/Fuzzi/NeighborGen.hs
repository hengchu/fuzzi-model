module Data.Fuzzi.NeighborGen where

import Test.QuickCheck
import System.Random
import Control.Monad

class Neighbor a where
  type Element a :: *

  left  :: a -> Element a
  right :: a -> Element a

data PairWiseL1List a = PairWiseL1List {
  dataAndDiff   :: [(a, a)]
  , diff     :: a
  } deriving (Show, Eq, Ord)

pairWiseL1 :: forall a. (Fractional a, Random a, Arbitrary a) => a -> Gen (PairWiseL1List a)
pairWiseL1 diff = do
  len <- choose (3, 7)
  xs <- replicateM len (choose (0.0, 1.0))
  ds <- replicateM len (choose (-diff, diff))
  return (PairWiseL1List (zip xs ds) diff)

shrinkPairWiseL1 :: PairWiseL1List a -> [PairWiseL1List a]
shrinkPairWiseL1 (PairWiseL1List xs diff) =
  filter (not . null . dataAndDiff) $
    PairWiseL1List <$> shrinkList (\x -> [x]) xs <*> pure diff

instance (Num a) => Neighbor (PairWiseL1List a) where
  type Element (PairWiseL1List a) = [a]
  left  = map fst . dataAndDiff
  right = map (uncurry (+)) . dataAndDiff

instance Foldable PairWiseL1List where
  foldMap f xs = foldMap f (map fst $ dataAndDiff xs)
