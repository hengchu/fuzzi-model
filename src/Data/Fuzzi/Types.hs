module Data.Fuzzi.Types where

import Data.Fuzzi.IfCxt
import Type.Reflection

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

class ( Boolean  (TestResult list)
      , Typeable (Elem list)
      , Typeable list
      ) => ListLike list where
  type Elem       list :: *
  type TestResult list :: *

  nil   :: list
  cons  :: Elem list -> list -> list
  snoc  :: list -> Elem list -> list
  isNil :: list -> TestResult list

-- |This constraint is only satisfied by numeric datatypes supported in Fuzzi.
class (Ordered a, Num a, Typeable a) => Numeric (a :: *)
class (Numeric a, Fractional a) => FracNumeric (a :: *)
class (Numeric a, LiteIntegral a) => IntNumeric (a :: *)

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

instance Typeable a => ListLike [a] where
  type Elem [a] = a
  type TestResult [a] = Bool

  nil = []
  cons = (:)
  snoc xs x = xs ++ [x]
  isNil [] = True
  isNil _  = False

instance {-# OVERLAPS #-} FuzziType Double
instance {-# OVERLAPS #-} FuzziType Bool
instance {-# OVERLAPS #-} FuzziType Int
instance {-# OVERLAPPABLE #-}
  ( ListLike list
  , FuzziType (Elem list)
  , Typeable list
  , Show list) => FuzziType list

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