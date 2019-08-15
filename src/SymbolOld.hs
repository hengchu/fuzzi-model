module Symbol where

import Text.Read (readMaybe)
import Control.Monad.Reader
import Control.Monad.State
import Data.Coerce
import SimpleSMT
import Type.Reflection
import Types

newtype RealExpr = RealExpr { getRealExpr :: SExpr }
  deriving (Show, Eq, Ord)

newtype BoolExpr = BoolExpr { getBoolExpr :: SExpr }
  deriving (Show, Eq, Ord)

newtype SymbolicT m a = SymbolicT { runSymbolicT_ :: ReaderT Solver (StateT Int m) a }
  deriving (Functor, Applicative, Monad, MonadIO) via (ReaderT Solver (StateT Int m))
  deriving (MonadReader Solver)
  deriving (MonadState Int)
  deriving (Typeable)

defaultZ3Solver :: IO Solver
defaultZ3Solver = do
  logger <- newLogger 0
  solver <- newSolver "z3" ["-smt2", "-in"] (Just logger)
  setOption solver ":pp.decimal" "false"
  return solver

runSymbolicT :: (MonadIO m) => SymbolicT m a -> m a
runSymbolicT m = do
  s <- liftIO defaultZ3Solver
  evalStateT (runReaderT (runSymbolicT_ m) s) 0

instance MonadTrans SymbolicT where
  lift m = SymbolicT (lift (lift m))

fresh :: (Monad m) => String -> SymbolicT m String
fresh namePrefix = do
  counter <- get
  modify (+1)
  return (namePrefix ++ show counter)

nameOfReal :: RealExpr -> Maybe String
nameOfReal (RealExpr x) =
  case x of
    Atom name -> Just name
    _ -> Nothing

nameOfBool :: BoolExpr -> Maybe String
nameOfBool (BoolExpr x) =
  case x of
    Atom name -> Just name
    _ -> Nothing

sRealNamed :: String -> RealExpr
sRealNamed = RealExpr . Atom

sReal :: (MonadIO m) => String -> SymbolicT m RealExpr
sReal name = do
  solver <- ask
  realSym <- liftIO $ declare solver name tReal
  return (RealExpr realSym)

getRealValue :: (MonadIO m) => String -> SymbolicT m (Maybe Rational)
getRealValue name = do
  solver <- ask
  val <- liftIO $ getConst solver name
  case val of
    Real v -> return (Just v)
    Other (Atom str) -> return (fmap (toRational @Double) (readMaybe str))
    _ -> return Nothing

sBool :: (MonadIO m) => String -> SymbolicT m BoolExpr
sBool name = do
  solver <- ask
  realSym <- liftIO $ declare solver name tReal
  return (BoolExpr realSym)

laplaceSymbolic :: (MonadIO m) => RealExpr -> Double -> SymbolicT m RealExpr
laplaceSymbolic _ _ = do
  name <- fresh "lap"
  sReal name

gaussianSymbolic :: (MonadIO m) => RealExpr -> Double -> SymbolicT m RealExpr
gaussianSymbolic _ _ = do
  name <- fresh "gauss"
  sReal name

assert :: (MonadIO m) => BoolExpr -> SymbolicT m ()
assert (BoolExpr cond) = do
  solver <- ask
  liftIO $ SimpleSMT.assert solver cond

assertAndTrack :: (MonadIO m) => String -> BoolExpr -> SymbolicT m ()
assertAndTrack name (BoolExpr cond) = do
  solver <- ask
  liftIO $ SimpleSMT.assert solver (named name cond)

check :: (MonadIO m) => SymbolicT m Result
check = do
  solver <- ask
  liftIO $ SimpleSMT.check solver

getUnsatCore :: (MonadIO m) => SymbolicT m [String]
getUnsatCore = do
  solver <- ask
  liftIO $ SimpleSMT.getUnsatCore solver

setLogic :: (MonadIO m) => String -> SymbolicT m ()
setLogic logic = do
  solver <- ask
  liftIO $ SimpleSMT.setLogic solver logic

instance (MonadIO m, Typeable m) => MonadDist (SymbolicT m) where
  type NumDomain (SymbolicT m) = RealExpr
  laplace  = laplaceSymbolic
  gaussian = gaussianSymbolic

instance Num RealExpr where
  (+) = coerce add
  (-) = coerce sub
  (*) = coerce mul
  abs = coerce SimpleSMT.abs
  signum a = RealExpr
             $ ite (getRealExpr a `gt` real 0)
                   (real 1)
                   (ite (getRealExpr a `eq` real 0)
                        (real 0)
                        (real (-1))
                   )
  fromInteger v = RealExpr (real (fromInteger v))

instance Fractional RealExpr where
  (/) = coerce SimpleSMT.div
  fromRational = RealExpr . real . fromRational

instance Boolean BoolExpr where
  and = coerce SimpleSMT.and
  or  = coerce SimpleSMT.or
  neg = coerce SimpleSMT.not

instance Ordered RealExpr where
  type CmpResult RealExpr = BoolExpr
  (%<)  = coerce lt
  (%<=) = coerce leq
  (%>)  = coerce gt
  (%>=) = coerce geq
  (%==) = coerce eq
  a %/= b = Types.neg (a %== b)

instance Numeric     RealExpr
instance FracNumeric RealExpr
