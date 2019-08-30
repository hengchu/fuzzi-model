module Data.Fuzzi.Distribution where

import Control.Monad
import Control.Monad.State.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State hiding (modify)
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Random.Distribution.Normal
import Data.Random.Distribution.Uniform
import Data.Random.RVar
import Data.Sequence
import Type.Reflection
import Data.Fuzzi.Types
import qualified Control.Monad.Trans.Class as MT
import qualified Data.Map.Strict as M
import qualified Data.Random as R
import Control.Monad.Catch
import Control.Monad.IO.Class

newtype ConcreteDist a = ConcreteDist { runConcreteDist :: RVarT IO a }
  deriving (Functor, Applicative, Monad) via (RVarT IO)
  deriving MonadIO via (RVarT IO)

data Trace :: * -> * where
  TrLaplace  :: a -> Double -> a -> Trace a
  TrGaussian :: a -> Double -> a -> Trace a
  deriving (Show, Eq, Ord, Functor)

type DProvenance k = DistributionProvenance k

-- |Type parameter 'k' is the type of the result. 'Buckets' maps results
-- identical up to provenance into the actual value of the result, paired with
-- the profiled trace of that execution.
type Buckets k = M.Map (DProvenance k) [(k, Seq (Trace Double))]
type BucketsNoProvenance k = M.Map k [(k, Seq (Trace Double))]

newtype TracedDist a =
  TracedDist { runTracedDist_ :: StateT (Seq (Trace Double)) ConcreteDist a }
  deriving (Functor, Applicative, Monad)
    via (StateT (Seq (Trace Double)) ConcreteDist)
  deriving (MonadIO, MonadState (Seq (Trace Double)))
    via (StateT (Seq (Trace Double)) ConcreteDist)

laplaceConcrete :: Double -> Double -> ConcreteDist Double
laplaceConcrete center width = ConcreteDist $ do
  r <- uniformT (-0.5) 0.5
  let positive = r > 0
  let sample = if positive
               then width * log (1 - 2 * abs r)
               else -width * log (1 - 2 * abs r)
  return $ center + sample

gaussianConcrete :: Double -> Double -> ConcreteDist Double
gaussianConcrete mean stddev =
  ConcreteDist $ normalT mean stddev

laplaceTraced :: WithDistributionProvenance Double
              -> Double
              -> TracedDist (WithDistributionProvenance Double)
laplaceTraced center width = do
  let centerValue = value center
  lapSample <- (TracedDist . MT.lift)
    ((laplaceConcrete centerValue width))
  let prov  = Laplace (provenance center) width
  let trace = TrLaplace centerValue width lapSample
  modify (|> trace)
  return (WithDistributionProvenance lapSample prov)

gaussianTraced :: WithDistributionProvenance Double
              -> Double
              -> TracedDist (WithDistributionProvenance Double)
gaussianTraced center width = do
  let centerValue = value center
  gaussSample <- (TracedDist . MT.lift)
    ((gaussianConcrete centerValue width))
  let prov  = Gaussian (provenance center) width
  let trace = TrGaussian centerValue width gaussSample
  modify (|> trace)
  return (WithDistributionProvenance gaussSample prov)

sampleConcrete :: ConcreteDist a -> IO a
sampleConcrete = R.sample . runConcreteDist

sampleTraced :: TracedDist a -> IO (a, Seq (Trace Double))
sampleTraced = R.sample . runConcreteDist . flip runStateT mempty . runTracedDist_

newtype NoRandomness a = NoRandomness { runNoRandomness :: a }
  deriving (Functor, Applicative, Monad, Show1)
  via Identity
  deriving (Show, Eq, Ord)

laplaceNoRandomness :: Double -> Double -> NoRandomness Double
laplaceNoRandomness center _ = NoRandomness center

gaussianNoRandomness :: Double -> Double -> NoRandomness Double
gaussianNoRandomness center _ = NoRandomness center

data ArithOp = Add | Mult | Sub | Div
  deriving (Show, Eq, Ord)

data UOp = Abs | Sign
  deriving (Show, Eq, Ord)

data DistributionProvenance (a :: *) where
  Deterministic :: (NotList a) => a
                -> DistributionProvenance a
  ListEmpty     :: DistributionProvenance [a]
  ListCons      :: (Show a, Eq a, Ord a)
                => DistributionProvenance a
                -> DistributionProvenance [a]
                -> DistributionProvenance [a]
  ListSnoc      :: (Show a, Eq a, Ord a)
                => DistributionProvenance [a]
                -> DistributionProvenance a
                -> DistributionProvenance [a]
  Laplace       :: (NotList a) => DistributionProvenance a
                -> Double
                -> DistributionProvenance a
  Gaussian      :: (NotList a) => DistributionProvenance a
                -> Double
                -> DistributionProvenance a
  Arith         :: (NotList a) => DistributionProvenance a
                -> ArithOp
                -> DistributionProvenance a
                -> DistributionProvenance a
  Unary         :: (NotList a) => UOp
                -> DistributionProvenance a
                -> DistributionProvenance a

deriving instance (Show a) => Show (DistributionProvenance a)
deriving instance (Eq a) => Eq (DistributionProvenance a)
deriving instance (Ord a) => Ord (DistributionProvenance a)
deriving instance Typeable DistributionProvenance

instance (NotList a, Num a) => Num (DistributionProvenance a) where
  a + b         = Arith a Add  b
  a * b         = Arith a Mult b
  a - b         = Arith a Sub  b
  abs           = Unary Abs
  signum        = Unary Sign
  fromInteger v = Deterministic (fromInteger v)

instance (NotList a, Fractional a) => Fractional (DistributionProvenance a) where
  a / b          = Arith a Div b
  fromRational v = Deterministic (fromRational v)

data WithDistributionProvenance a =
  WithDistributionProvenance { value :: a
                             , provenance :: DistributionProvenance a
                             }
  deriving (Eq, Ord, Typeable)

instance Show a => Show (WithDistributionProvenance a) where
  show a = show (value a)

instance (NotList a, Num a) => Num (WithDistributionProvenance a) where
  a + b = WithDistributionProvenance (value a + value b) (provenance a + provenance b)
  a * b = WithDistributionProvenance (value a * value b) (provenance a * provenance b)
  a - b = WithDistributionProvenance (value a - value b) (provenance a - provenance b)
  abs a = WithDistributionProvenance (abs (value a)) (abs (provenance a))
  signum a = WithDistributionProvenance (signum (value a)) (signum (provenance a))
  fromInteger v = WithDistributionProvenance (fromInteger v) (fromInteger v)

instance (NotList a, Fractional a) => Fractional (WithDistributionProvenance a) where
  a / b = WithDistributionProvenance (value a / value b) (provenance a / provenance b)
  fromRational v = WithDistributionProvenance (fromRational v) (fromRational v)

instance Ordered a => Ordered (WithDistributionProvenance a) where
  type CmpResult (WithDistributionProvenance a) = CmpResult a
  a %<  b = value a %<  value b
  a %<= b = value a %<= value b
  a %>  b = value a %>  value b
  a %>= b = value a %>= value b
  a %== b = value a %== value b
  a %/= b = value a %/= value b

unsnoc :: [a] -> Maybe ([a], a)
unsnoc xs =
  case Prelude.reverse xs of
    x:xs' -> Just (Prelude.reverse xs', x)
    _     -> Nothing

instance (Show a, Eq a, Ord a, Typeable a)
  => ListLike (WithDistributionProvenance [a]) where
  type Elem       (WithDistributionProvenance [a]) =
    WithDistributionProvenance (Elem [a])
  type TestResult (WithDistributionProvenance [a])   = TestResult [a]
  type LengthResult (WithDistributionProvenance [a]) = LengthResult [a]

  nil       = WithDistributionProvenance nil ListEmpty
  cons x xs = WithDistributionProvenance
                (cons (value x) (value xs))
                (ListCons (provenance x) (provenance xs))
  snoc xs x = WithDistributionProvenance
                (snoc (value xs) (value x))
                (ListSnoc (provenance xs) (provenance x))
  isNil xs  = isNil (value xs)

  filter_ pred xs =
    case (value xs, provenance xs) of
      ([]  , ListEmpty)     -> xs
      (x:xs, ListCons p ps) ->
        if pred (WithDistributionProvenance x p)
        then let rest = filter_ pred (WithDistributionProvenance xs ps)
                 v'   = value rest
                 p'   = provenance rest
             in WithDistributionProvenance (x:v') (ListCons p p')
        else filter_ pred (WithDistributionProvenance xs ps)
      (unsnoc -> Just (xs, x), ListSnoc ps p) ->
        let rest = filter_ pred (WithDistributionProvenance xs ps)
        in if pred (WithDistributionProvenance x p)
           then snoc rest (WithDistributionProvenance x p)
           else rest
      _ -> error $ "WithDistributionProvenance: list value "
                   ++ "and provenance are not synchronized, "
                   ++ "i.e. they are not built with cons and snoc"
  length_ = length_ . value

instance (NotList a, Numeric a)     => Numeric (WithDistributionProvenance a)
instance (NotList a, FracNumeric a) => FracNumeric (WithDistributionProvenance a)
instance {-# OVERLAPPABLE #-} FuzziType a   => FuzziType (WithDistributionProvenance a)
instance {-# OVERLAPS #-}     FuzziType a   => FuzziType (WithDistributionProvenance [a])

instance MonadDist ConcreteDist where
  type NumDomain ConcreteDist = Double
  laplace = laplaceConcrete
  gaussian = gaussianConcrete

instance MonadDist NoRandomness where
  type NumDomain NoRandomness = Double
  laplace = laplaceNoRandomness
  gaussian = gaussianNoRandomness

instance MonadDist TracedDist where
  type NumDomain TracedDist = WithDistributionProvenance Double
  laplace  = laplaceTraced
  gaussian = gaussianTraced

instance MonadAssert TracedDist where
  type BoolType TracedDist = Bool
  assertTrue _ = return ()

instance Matchable a b => Matchable a (WithDistributionProvenance b) where
  match a b = match a (value b)

instance MonadThrow TracedDist where
  throwM = liftIO . throwM
