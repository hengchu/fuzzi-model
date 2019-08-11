module Types where

import Type.Reflection

-- |This constraint is only satisfied by first-class datatypes supported in
-- Fuzzi.
class FuzziType (a :: *)

-- |Order operators in the semantic domain.
class (Boolean (CmpResult a), Typeable a) => Ordered (a :: *) where
  type CmpResult a :: *
  (%<)  :: a -> a -> CmpResult a
  (%<=) :: a -> a -> CmpResult a
  (%>)  :: a -> a -> CmpResult a
  (%>=) :: a -> a -> CmpResult a
  (%==) :: a -> a -> CmpResult a
  (%/=) :: a -> a -> CmpResult a

-- |This constraint is only satisfied by numeric datatypes supported in Fuzzi.
class (Ordered a, Num a, Typeable a) => Numeric (a :: *)
class (Numeric a, Fractional a) => FracNumeric (a :: *)

-- |Boolean operators in the semantic domain.
class (Typeable a) => Boolean (a :: *) where
  and :: a -> a -> a
  or  :: a -> a -> a
  neg :: a -> a

-- |Sample instructions in the semantic domain.
class (Monad m, Typeable m, FracNumeric (NumDomain m)) => MonadDist m where
  type NumDomain m :: *
  laplace  :: NumDomain m -> Double -> m (NumDomain m)
  gaussian :: NumDomain m -> Double -> m (NumDomain m)

type Distribution m a = (MonadDist m, NumDomain m ~ a, FuzziType a, FracNumeric a)


instance Boolean Bool where
  and = (&&)
  or  = (||)
  neg = not

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
  (%<)  = (<)
  (%<=) = (<=)
  (%>)  = (>)
  (%>=) = (>=)
  (%==) = (==)
  (%/=) = (/=)

instance FuzziType Double
instance FuzziType Bool
instance FuzziType Int

instance Numeric Double
instance FracNumeric Double
instance Numeric Int
