module Term where

import Control.Applicative.Free
import Data.Proxy
import Model
import Types

data FuzziF :: (* -> *) -> * -> * where
  FPure    :: a -> FuzziF d a
  FAp      :: FuzziF d (a -> b)
           -> FuzziF d a
           -> FuzziF d b
  FWithSample :: (Value a) => FuzziF d a -> (a -> FuzziF d b) -> FuzziF d b
  FLaplace :: (Show a, Model domain a)
           => FuzziF domain a -- ^center
           -> Double -- ^width
           -> FuzziF domain a
  FGaussian :: (Show a, Model domain a)
            => FuzziF domain a -- ^mean
            -> Double -- ^stddev
            -> FuzziF domain a
  FIf :: FuzziF domain Bool
      -> FuzziF domain a
      -> FuzziF domain a
      -> FuzziF domain a

instance Functor (FuzziF domain) where
  fmap f (FPure a) = FPure (f a)
  fmap f (FLaplace center width) =
    FAp (FPure f) (FLaplace center width)
  fmap f (FGaussian center width) =
    FAp (FPure f) (FGaussian center width)
  fmap f (FIf cond truecmd falsecmd) =
    FIf cond (fmap f truecmd) (fmap f falsecmd)
  fmap f (FWithSample a g) =
    FWithSample a (\x -> fmap f (g x))
  fmap f (FAp g a) =
    FAp (FPure f) (FAp g a)

instance Applicative (FuzziF domain) where
  pure  = FPure
  (<*>) = FAp

type Fuzzi domain = Ap (FuzziF domain)

laplace :: (Show a, Model domain a) => Fuzzi domain a -> Double -> Fuzzi domain a
laplace center width =
  liftAp $ FLaplace (retractAp center) width

gaussian :: (Show a, Model domain a) => Fuzzi domain a -> Double -> Fuzzi domain a
gaussian center width =
  liftAp $ FGaussian (retractAp center) width

withSample :: (Value a) => Fuzzi domain a -> (a -> Fuzzi domain b) -> Fuzzi domain b
withSample a f =
  liftAp $ FWithSample (retractAp a) (fmap retractAp f)

fif :: Fuzzi domain Bool -> Fuzzi domain a -> Fuzzi domain a -> Fuzzi domain a
fif cond truecmd falsecmd =
  liftAp $ FIf (retractAp cond) (retractAp truecmd) (retractAp falsecmd)
