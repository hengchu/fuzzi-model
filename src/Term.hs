module Term where

import Control.Applicative.Free
import Data.Proxy
import Model
import Types

data FuzziF :: (* -> *) -> * -> * -> * where
  FPure    :: a -> FuzziF d bool a
  FAp      :: FuzziF d bool (a -> b)
           -> FuzziF d bool a
           -> FuzziF d bool b
  FWithSample :: (Value a) => FuzziF d bool a -> (a -> FuzziF d bool b) -> FuzziF d bool b
  FLaplace :: (Show a, Model domain a)
           => FuzziF domain bool a -- ^center
           -> Double -- ^width
           -> FuzziF domain bool a
  FGaussian :: (Show a, Model domain a)
            => FuzziF domain bool a -- ^mean
            -> Double -- ^stddev
            -> FuzziF domain bool a
  FIf :: FuzziF domain bool bool
      -> FuzziF domain bool a
      -> FuzziF domain bool a
      -> FuzziF domain bool a

instance Functor (FuzziF domain bool) where
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

instance Applicative (FuzziF domain bool) where
  pure  = FPure
  (<*>) = FAp

type Fuzzi domain bool = Ap (FuzziF domain bool)

laplace :: (Show a, Model domain a) => Fuzzi domain bool a -> Double -> Fuzzi domain bool a
laplace center width =
  liftAp $ FLaplace (retractAp center) width

gaussian :: (Show a, Model domain a) => Fuzzi domain bool a -> Double -> Fuzzi domain bool a
gaussian center width =
  liftAp $ FGaussian (retractAp center) width

withSample :: (Value a) => Fuzzi domain bool a -> (a -> Fuzzi domain bool b) -> Fuzzi domain bool b
withSample a f =
  liftAp $ FWithSample (retractAp a) (fmap retractAp f)

fif :: Fuzzi domain bool bool -> Fuzzi domain bool a -> Fuzzi domain bool a -> Fuzzi domain bool a
fif cond truecmd falsecmd =
  liftAp $ FIf (retractAp cond) (retractAp truecmd) (retractAp falsecmd)
