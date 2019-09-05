module Data.Fuzzi.Types where

import Control.Monad.Catch
import Data.Fuzzi.IfCxt
import Data.Kind (Constraint)
import GHC.TypeLits
import Type.Reflection
import qualified Data.Map.Merge.Strict as MM
import qualified Data.Map.Strict as M

-- |This constraint is only satisfied by first-class datatypes supported in
-- Fuzzi.
class (Typeable a, Show a) => FuzziType (a :: *)

-- |Order operators in the semantic domain.
class (Boolean (CmpResult a), Typeable a) => Ordered (a :: *) where
  type CmpResult a :: *
  (%<)  :: a -> a -> CmpResult a
  (%<=) :: a -> a -> CmpResult a
  (%>)  :: a -> a -> CmpResult a
  (%>=) :: a -> a -> CmpResult a
  (%==) :: a -> a -> CmpResult a
  (%/=) :: a -> a -> CmpResult a

class LiteIntegral (a :: *) where
  idiv :: a -> a -> a
  imod :: a -> a -> a

instance LiteIntegral Int where
  idiv = div
  imod = mod

{-
class ( Typeable (LengthResult list)
      , Typeable (Elem list)
      , Typeable list
      ) => ListLike list where
  type Elem         list :: *
  type TestResult   list :: *
  type LengthResult list :: *

  nil   :: list
  cons  :: Elem list -> list -> list
  snoc  :: list -> Elem list -> list
  isNil :: list -> TestResult list

  length_  :: list -> LengthResult list
  filter_  :: (Elem list -> TestResult list) -> list -> list
-}

-- |This constraint is only satisfied by numeric datatypes supported in Fuzzi.
class (Ordered a, Num a, Typeable a) => Numeric (a :: *)
class (Numeric a, Fractional a)      => FracNumeric (a :: *)
class (Numeric a, LiteIntegral a)    => IntNumeric (a :: *)

-- |Boolean operators in the semantic domain.
class (Typeable a) => Boolean (a :: *) where
  and :: a -> a -> a
  or  :: a -> a -> a
  neg :: a -> a

class Boolean a => ConcreteBoolean (a :: *) where
  toBool   :: a -> Bool
  fromBool :: Bool -> a

-- |Sample instructions in the semantic domain.
class (Monad m, Typeable m, FracNumeric (NumDomain m)) => MonadDist m where
  type NumDomain m :: *
  laplace   ::             NumDomain m -> Double -> m (NumDomain m)
  laplace'  :: Rational -> NumDomain m -> Double -> m (NumDomain m)
  gaussian  ::             NumDomain m -> Double -> m (NumDomain m)
  gaussian' :: Rational -> NumDomain m -> Double -> m (NumDomain m)

class (Monad m, Typeable m, Boolean (BoolType m), MonadThrow m) => MonadAssert m where
  type BoolType m :: *
  assertTrue  :: BoolType m -> m ()
  assertFalse :: BoolType m -> m ()
  assertFalse v = assertTrue (neg v)

class Matchable concrete symbolic where
  match :: concrete -> symbolic -> Bool

type Distribution m a    = (MonadDist m, NumDomain m ~ a, FuzziType a, FracNumeric a)
type Assertion    m bool = (MonadAssert m, BoolType m ~ bool, IfCxt (ConcreteBoolean bool))
type FuzziLang    m a    = (Distribution m a, Assertion m (CmpResult a))

instance Boolean Bool where
  and = (&&)
  or  = (||)
  neg = not

instance ConcreteBoolean Bool where
  toBool   = id
  fromBool = id


instance {-# OVERLAPS #-} IfCxt (ConcreteBoolean Bool) where
  ifCxt _ t _ = t

instance Ordered Double where
  type CmpResult Double = Bool
  (%<)  = (<)
  (%<=) = (<=)
  (%>)  = (>)
  (%>=) = (>=)
  (%==) = (==)
  (%/=) = (/=)

instance Ordered Int where
  type CmpResult Int = Bool
  (%<)  a b = fromBool $ (<) a b
  (%<=) a b = fromBool $ (<=) a b
  (%>)  a b = fromBool $ (>) a b
  (%>=) a b = fromBool $ (>=) a b
  (%==) a b = fromBool $ (==) a b
  (%/=) a b = fromBool $ (/=) a b

{-
instance (Typeable a) => ListLike [a] where
  type Elem         [a] = a
  type TestResult   [a] = Bool
  type LengthResult [a] = Int

  nil = []
  cons = (:)
  snoc xs x = xs ++ [x]
  isNil [] = True
  isNil _  = False

  filter_ = filter
  length_ = length
-}

instance FuzziType Double
instance FuzziType Bool
instance FuzziType Int
instance FuzziType a => FuzziType (PrivTree1D a)
instance FuzziType a => FuzziType [a]
instance FuzziType a => FuzziType (Maybe a)
instance FuzziType PrivTreeNode1D
instance (FuzziType a, FuzziType b) => FuzziType (a, b)

instance Numeric Double
instance FracNumeric Double
instance Numeric Int
instance IntNumeric Int

instance Matchable Int Int where
  match a b = a == b

instance Matchable Integer Integer where
  match a b = a == b

instance Matchable Bool Bool where
  match a b = a == b

instance ( Matchable a b
         , Matchable c d
         ) => Matchable (a,c) (b,d) where
  match (a,b) (c,d) = match a c && match b d

instance Matchable a b => Matchable (Maybe a) (Maybe b) where
  match (Just a) (Just b) = match a b
  match Nothing  Nothing  = True
  match _        _        = False

instance Matchable a b => Matchable [a] [b] where
  match []     []     = True
  match (x:xs) (y:ys) = match x y && match xs ys
  match _      _      = False

data PrivTree1DDir = LeftDir | RightDir
  deriving (Show, Eq, Ord)

newtype PrivTreeNode1D = PrivTreeNode1D [PrivTree1DDir]
  deriving (Show, Eq, Ord)

newtype PrivTree1D count = PrivTree1D { getPrivTree1D :: M.Map PrivTreeNode1D count }
  deriving (Show, Eq, Ord)     via (M.Map PrivTreeNode1D count)
  deriving (Functor, Foldable) via (M.Map PrivTreeNode1D)

split :: PrivTreeNode1D -> (PrivTreeNode1D, PrivTreeNode1D)
split (PrivTreeNode1D dirs) = ( PrivTreeNode1D (dirs ++ [LeftDir])
                              , PrivTreeNode1D (dirs ++ [RightDir])
                              )

rootNode :: PrivTreeNode1D
rootNode = PrivTreeNode1D []

emptyTree :: PrivTree1D count
emptyTree = PrivTree1D M.empty

update :: PrivTreeNode1D -> count -> PrivTree1D count -> PrivTree1D count
update k v (PrivTree1D tree) = PrivTree1D $ M.insert k v tree

depth :: (Num count) => PrivTreeNode1D -> count
depth (PrivTreeNode1D dirs) = fromIntegral (length dirs)

endpoints :: PrivTreeNode1D -> (Double, Double)
endpoints (PrivTreeNode1D dirs) = go dirs 0 1
  where go []            start end = (start, end)
        go (LeftDir:xs)  start end = go xs start               ((start + end) / 2)
        go (RightDir:xs) start end = go xs ((start + end) / 2) end

countPoints :: (Num count) => [Double] -> PrivTreeNode1D -> count
countPoints points node =
  fromIntegral $ length (filter (\x -> leftEnd <= x && x < rightEnd) points)
  where (leftEnd, rightEnd) = endpoints node

instance Matchable a b => Matchable (PrivTree1D a) (PrivTree1D b) where
  match (PrivTree1D a) (PrivTree1D b) =
    Prelude.and (MM.merge whenMissing whenMissing whenMatched a b)
    where whenMissing = MM.mapMissing (\_ _ -> False)
          whenMatched = MM.zipWithMatched (const match) -- \_ a b -> match a b

type family NotList (t :: *) :: Constraint where
  NotList ([] a) = TypeError (
                       'Text "The type "
                       ':<>: 'ShowType ([] a)
                       ':<>: 'Text " seems to be wrapped in a list type constructor,"
                       ':<>: 'Text " please use cons/snoc to build List of provenances.")
  NotList _      = ()
