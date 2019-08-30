module Data.Fuzzi.Types where

import Data.Fuzzi.IfCxt
import Data.Kind (Constraint)
import GHC.TypeLits
import Type.Reflection
import qualified Data.Map.Merge.Strict as MM
import qualified Data.Map.Strict as M

-- |This constraint is only satisfied by first-class datatypes supported in
-- Fuzzi.
class (Typeable a, Show a) => FuzziType (a :: *)

class Embed f where
  embed :: (FuzziType a) => a -> f a

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

-- | 'Option' is necessary because 'Maybe' is not a 'Representable' functor, so
-- we use the extra field to store whether a value exists in this 'Option' or
-- not.
data OptionF f a = OptionF {
  isSome :: f Bool
  , fromSome :: a
  }

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

  uncons :: (Embed f) => list -> OptionF f (Elem list, list)

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
  laplace  :: NumDomain m -> Double -> m (NumDomain m)
  gaussian :: NumDomain m -> Double -> m (NumDomain m)

class (Monad m, Typeable m, Boolean (BoolType m)) => MonadAssert m where
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

instance (Inhabited a, Typeable a) => ListLike [a] where
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

  uncons []     = OptionF (embed False) (inhabitant, [])
  uncons (x:xs) = OptionF (embed True)  (x, xs)

instance FuzziType Double
instance FuzziType Bool
instance FuzziType Int
instance FuzziType a => FuzziType (PrivTree1D a)
instance FuzziType a => FuzziType [a]

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

emptyTree :: PrivTree1D count
emptyTree = PrivTree1D M.empty

update :: PrivTreeNode1D -> count -> PrivTree1D count -> PrivTree1D count
update k v (PrivTree1D tree) = PrivTree1D $ M.insert k v tree

depth :: PrivTreeNode1D -> PrivTree1D count -> Int
depth (PrivTreeNode1D dirs) _ = length dirs

depth' :: (FracNumeric a) => PrivTreeNode1D -> PrivTree1D count -> a
depth' node tree = fromIntegral (depth node tree)

endpoints :: (FracNumeric a) => PrivTreeNode1D -> (a, a)
endpoints (PrivTreeNode1D dirs) = go dirs 0 1
  where go []            start end = (start, end)
        go (LeftDir:xs)  start end = go xs start               ((start + end) / 2)
        go (RightDir:xs) start end = go xs ((start + end) / 2) end

countPoints :: ( FracNumeric (Elem listA)
               , CmpResult   (Elem listA) ~ TestResult listA
               , ListLike listA
               ) => listA -> PrivTreeNode1D -> LengthResult listA
countPoints points node =
  length_ (filter_ (\x -> (leftEnd %<= x) `Data.Fuzzi.Types.and` (x %< rightEnd)) points)
  where (leftEnd, rightEnd) = endpoints node

instance Matchable a b => Matchable (PrivTree1D a) (PrivTree1D b) where
  match (PrivTree1D a) (PrivTree1D b) =
    all id (MM.merge whenMissing whenMissing whenMatched a b)
    where whenMissing = MM.mapMissing (\_ _ -> False)
          whenMatched = MM.zipWithMatched (\_ -> match)

type family NotList (t :: *) :: Constraint where
  NotList ([] a) = TypeError (
                       'Text "The type "
                       ':<>: 'ShowType ([] a)
                       ':<>: 'Text " seems to be wrapped in a list type constructor,"
                       ':<>: 'Text " please use cons/snoc to build List of provenances.")
  NotList _      = ()

class Inhabited a where
  inhabitant :: a

instance Inhabited Int where
  inhabitant = 0

instance Inhabited Double where
  inhabitant = 0

instance Inhabited Bool where
  inhabitant = False

instance Inhabited [a] where
  inhabitant = []

instance Inhabited b => Inhabited (a -> b) where
  inhabitant = const inhabitant
