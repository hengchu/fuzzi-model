module Data.Fuzzi.Distribution where

import Control.Monad.State.Class
import Control.Monad.Trans.State hiding (modify, gets)
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Random.Distribution.Normal
import Data.Random.Distribution.Uniform
import Data.Random.RVar
import Data.Sequence
import Type.Reflection
import Data.Fuzzi.Types hiding (SymbolicExpr(..))
import qualified Control.Monad.Trans.Class as MT
import qualified Data.Map.Strict as M
import qualified Data.Random as R
import Control.Monad.Catch
import Control.Monad.IO.Class

class Eq (GetProvenance a) => HasProvenance a where
  type GetProvenance  a :: *
  type DropProvenance a :: *
  getProvenance  :: a -> GetProvenance a
  dropProvenance :: a -> DropProvenance a

newtype ConcreteDist a = ConcreteDist { runConcreteDist :: RVarT IO a }
  deriving (Functor, Applicative, Monad) via (RVarT IO)
  deriving MonadIO via (RVarT IO)

data Trace :: * -> * where
  TrLaplace  :: a -> Double -> a -> Trace a
  TrGaussian :: a -> Double -> a -> Trace a
  deriving (Show, Eq, Ord, Functor)

-- |Type parameter 'k' is the type of the result. 'Buckets' maps results
-- identical up to provenance into the actual value of the result, paired with
-- the profiled trace of that execution.
type Buckets k = M.Map (GetProvenance k) [(k, Seq (Trace Double))]

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
    (laplaceConcrete centerValue width)
  traceIdx <- gets Data.Sequence.length
  let prov  = Laplace traceIdx (provenance center) width
  let trace = TrLaplace centerValue width lapSample
  modify (|> trace)
  return (WithDistributionProvenance lapSample prov)

gaussianTraced :: WithDistributionProvenance Double
              -> Double
              -> TracedDist (WithDistributionProvenance Double)
gaussianTraced center width = do
  let centerValue = value center
  gaussSample <- (TracedDist . MT.lift)
    (gaussianConcrete centerValue width)
  traceIdx <- gets Data.Sequence.length
  let prov  = Gaussian traceIdx (provenance center) width
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
  Deterministic :: a -> DistributionProvenance a
  Laplace       :: Int
                -> DistributionProvenance a
                -> Double
                -> DistributionProvenance a
  Gaussian      :: Int
                -> DistributionProvenance a
                -> Double
                -> DistributionProvenance a
  Arith         :: DistributionProvenance a
                -> ArithOp
                -> DistributionProvenance a
                -> DistributionProvenance a
  Unary         :: UOp
                -> DistributionProvenance a
                -> DistributionProvenance a
  deriving (Show, Eq, Ord)

{-
deriving instance (Show a) => Show (DistributionProvenance a)
deriving instance (Eq a) => Eq (DistributionProvenance a)
deriving instance (Ord a) => Ord (DistributionProvenance a)
deriving instance Typeable DistributionProvenance
-}

instance Num a => Num (DistributionProvenance a) where
  a + b         = Arith a Add  b
  a * b         = Arith a Mult b
  a - b         = Arith a Sub  b
  abs           = Unary Abs
  signum        = Unary Sign
  fromInteger v = Deterministic (fromInteger v)

instance Fractional a => Fractional (DistributionProvenance a) where
  a / b          = Arith a Div b
  fromRational v = Deterministic (fromRational v)

data WithDistributionProvenance a =
  WithDistributionProvenance { value :: a
                             , provenance :: DistributionProvenance a
                             }
  deriving ({-Show, -}Eq, Ord, Typeable)


instance Show a => Show (WithDistributionProvenance a) where
  show a = show (value a)

instance Num a => Num (WithDistributionProvenance a) where
  a + b = WithDistributionProvenance (value a + value b) (provenance a + provenance b)
  a * b = WithDistributionProvenance (value a * value b) (provenance a * provenance b)
  a - b = WithDistributionProvenance (value a - value b) (provenance a - provenance b)
  abs a = WithDistributionProvenance (abs (value a)) (abs (provenance a))
  signum a = WithDistributionProvenance (signum (value a)) (signum (provenance a))
  fromInteger v = WithDistributionProvenance (fromInteger v) (fromInteger v)

instance Fractional a => Fractional (WithDistributionProvenance a) where
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

instance Numeric a     => Numeric (WithDistributionProvenance a)
instance FracNumeric a => FracNumeric (WithDistributionProvenance a)
instance FuzziType a => FuzziType (WithDistributionProvenance a)

instance MonadDist ConcreteDist where
  type NumDomain ConcreteDist = Double
  laplace   = laplaceConcrete
  laplace'  = const laplaceConcrete
  gaussian  = gaussianConcrete
  gaussian' = const gaussianConcrete

instance MonadDist NoRandomness where
  type NumDomain NoRandomness = Double
  laplace   = laplaceNoRandomness
  laplace'  = const laplaceNoRandomness
  gaussian  = gaussianNoRandomness
  gaussian' = const gaussianNoRandomness

instance MonadDist TracedDist where
  type NumDomain TracedDist = WithDistributionProvenance Double
  laplace   = laplaceTraced
  laplace'  = const laplaceTraced
  gaussian  = gaussianTraced
  gaussian' = const gaussianTraced

instance MonadAssert TracedDist where
  type BoolType TracedDist = Bool
  assertTrue _ = return ()

matchProvenance :: Matchable a b
                 => DistributionProvenance a
                 -> DistributionProvenance b
                 -> Bool
matchProvenance (Deterministic _)          (Deterministic _)             = True
matchProvenance (Laplace idx center width) (Laplace idx' center' width') =
  idx == idx' && matchProvenance center center' && width == width'
matchProvenance (Gaussian idx center width) (Gaussian idx' center' width') =
  idx == idx' && matchProvenance center center' && width == width'
matchProvenance (Arith lhs op rhs) (Arith lhs' op' rhs') =
  op == op' && matchProvenance lhs lhs' && matchProvenance rhs rhs'
matchProvenance (Unary op operand) (Unary op' operand') =
  op == op' && matchProvenance operand operand'
matchProvenance _ _ = False

instance Matchable a RealExpr =>
  Matchable (WithDistributionProvenance a) RealExpr where
  match a b = match (value a) b

instance Matchable a b =>
  Matchable
    (WithDistributionProvenance a)
    (WithDistributionProvenance b) where
  match a b =
    let _provA = provenance a
        _provB = provenance b
    in match (value a) (value b) -- && matchProvenance provA provB

instance MonadThrow TracedDist where
  throwM = liftIO . throwM

instance HasProvenance (WithDistributionProvenance Double) where
  type GetProvenance  (WithDistributionProvenance Double) = DistributionProvenance Double
  type DropProvenance (WithDistributionProvenance Double) = Double
  getProvenance  = provenance
  dropProvenance = value

instance HasProvenance a => HasProvenance [a] where
  type GetProvenance  [a] = [GetProvenance a]
  type DropProvenance [a] = [DropProvenance a]
  getProvenance  = map getProvenance
  dropProvenance = map dropProvenance

instance HasProvenance a => HasProvenance (PrivTree1D a) where
  type GetProvenance  (PrivTree1D a) = PrivTree1D (GetProvenance a)
  type DropProvenance (PrivTree1D a) = PrivTree1D (DropProvenance a)
  getProvenance  = fmap getProvenance
  dropProvenance = fmap dropProvenance

instance HasProvenance a => HasProvenance (Maybe a) where
  type GetProvenance (Maybe a) = Maybe (GetProvenance a)
  type DropProvenance (Maybe a) = Maybe (DropProvenance a)
  getProvenance = fmap getProvenance
  dropProvenance = fmap dropProvenance

instance (HasProvenance a, HasProvenance b) => HasProvenance (a, b) where
  type GetProvenance (a, b) = (GetProvenance a, GetProvenance b)
  type DropProvenance (a, b) = (DropProvenance a, DropProvenance b)
  getProvenance (a, b)  = (getProvenance a, getProvenance b)
  dropProvenance (a, b) = (dropProvenance a, dropProvenance b)

instance HasProvenance () where
  type GetProvenance () = ()
  type DropProvenance () = ()
  getProvenance = id
  dropProvenance = id

instance HasProvenance Int where
  type GetProvenance Int = Int
  type DropProvenance Int = Int
  getProvenance = id
  dropProvenance = id

instance HasProvenance Integer where
  type GetProvenance Integer = Integer
  type DropProvenance Integer = Integer
  getProvenance = id
  dropProvenance = id

instance HasProvenance Bool where
  type GetProvenance Bool = Bool
  type DropProvenance Bool = Bool
  getProvenance = id
  dropProvenance = id

instance HasProvenance Double where
  type GetProvenance Double = Double
  type DropProvenance Double = Double
  getProvenance = id
  dropProvenance = id

instance SymbolicRepr a => SymbolicRepr (WithDistributionProvenance a) where
  merge = undefined

instance SEq
  (WithDistributionProvenance Double)
  (WithDistributionProvenance RealExpr) where
  symEq a b = symEq (value a) (value b)

instance SEq
  (WithDistributionProvenance Double) RealExpr where
  symEq a b = symEq (value a) b
