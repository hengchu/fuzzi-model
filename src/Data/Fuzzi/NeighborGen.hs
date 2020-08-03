{-# OPTIONS_HADDOCK hide #-}
module Data.Fuzzi.NeighborGen (
  Neighbor(..)
  , PairWiseL1List
  , pairWiseL1
  , pairWiseL1Sized
  , shrinkPairWiseL1
  , L1List
  , l1List
  , shrinkL1List
  , BagList
  , bagList
  , bagListSmall
  , bagListLarge
  , bagListLength
  , SensitiveCount
  , sensitiveCount
  , GeoFixedSensParam(..)
  , geoFixedSensParam
  , nonEmptyListOfGeoFixedSensParams
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
  } deriving (Eq, Ord)

instance (Show a, Num a) => Show (PairWiseL1List a) where
  show xs =
    let xs1 = left xs
        xs2 = right xs
    in "PairWiseL1List { left = " ++ show xs1 ++ ", right = " ++ show xs2 ++ " }"

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
pairWiseL1 = pairWiseL1Sized (3,7)

pairWiseL1Sized :: forall a.
                   ( Fractional a
                   , Random a
                   )
                => (Int, Int)
                -> a
                -> Gen (PairWiseL1List a)
pairWiseL1Sized sizeBounds diff = do
  len <- choose sizeBounds
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

bagList :: forall a. (Random a) => (Int, Int) -> (a, a) -> Int -> Gen (BagList a)
bagList (minLen, maxLen) (lower, upper) nDiff = do
  len <- choose (minLen, maxLen)
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

bagListSmall :: forall a. Random a => (a, a) -> Int -> Gen (BagList a)
bagListSmall = bagList (3, 4)

bagListLarge :: forall a. Random a => (a, a) -> Int -> Gen (BagList a)
bagListLarge = bagList (6, 8)

bagListLength :: BagList a -> (Int, Int)
bagListLength (BagList left right) = (length left, length right)

data SensitiveCount a = SensitiveCount a a
  deriving (Show, Eq, Ord)

sensitiveCount :: Integer -> Gen (SensitiveCount Integer)
sensitiveCount sens = do
  (NonNegative start) <- arbitrary
  a <- choose (start, start + sens)
  b <- choose (start, start + sens)
  return $ SensitiveCount a b

data GeoFixedSensParam a = GeoFixedSensParam a a Double Double
  deriving (Show, Eq, Ord)

geoFixedSensParam :: Gen (GeoFixedSensParam Integer)
geoFixedSensParam = do
  (sens :: Integer) <- choose (1, 5)
  (eps :: Double) <- choose (1.0, 8.0)
  (NonNegative start) <- arbitrary
  a <- choose (start, start + sens)
  b <- choose (start, start + sens)
  return $ GeoFixedSensParam a b (fromIntegral sens) eps

nonEmptyListOfGeoFixedSensParams :: Gen (NonEmptyList (GeoFixedSensParam Integer))
nonEmptyListOfGeoFixedSensParams = NonEmpty <$> listOf1 geoFixedSensParam

instance Num a => Neighbor (SensitiveCount a) where
  type Element (SensitiveCount a) = a
  left  (SensitiveCount a _) = a
  right (SensitiveCount _ b) = b

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
