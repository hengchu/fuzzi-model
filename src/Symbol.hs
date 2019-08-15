module Symbol where

{- HLINT ignore "Use newtype instead of data" -}

import Types
import Control.Monad.IO.Class
import System.IO.Unsafe
import qualified Z3.Base as Z3

_globalConfig :: Z3.Config
{-# NOINLINE _globalConfig #-}
_globalConfig = unsafePerformIO $ do
  cfg <- Z3.mkConfig
  return cfg

_globalContext :: Z3.Context
{-# NOINLINE _globalContext #-}
_globalContext = unsafePerformIO (Z3.mkContext _globalConfig)

_realSort :: Z3.Sort
{-# NOINLINE _realSort #-}
_realSort = unsafePerformIO (Z3.mkRealSort _globalContext)

data RealExpr = RealExpr { getRealExpr :: !Z3.AST }
data BoolExpr = BoolExpr { getBoolExpr :: !Z3.AST }

instance Show RealExpr where
  show (RealExpr a) = unsafePerformIO $ Z3.astToString _globalContext a

instance Show BoolExpr where
  show (BoolExpr a) = unsafePerformIO $ Z3.astToString _globalContext a

instance Eq RealExpr where
  (RealExpr a) == (RealExpr b) = unsafePerformIO $ Z3.isEqAST _globalContext a b

instance Eq BoolExpr where
  (BoolExpr a) == (BoolExpr b) = unsafePerformIO $ Z3.isEqAST _globalContext a b

compareHash :: Z3.AST -> Z3.AST -> IO Ordering
compareHash a b = do
  hashA <- Z3.getASTHash _globalContext a
  hashB <- Z3.getASTHash _globalContext b
  return (compare hashA hashB)

instance Ord RealExpr where
  compare (RealExpr a) (RealExpr b) = unsafePerformIO (compareHash a b)

instance Ord BoolExpr where
  compare (BoolExpr a) (BoolExpr b) = unsafePerformIO (compareHash a b)

sReal :: MonadIO m => String -> m RealExpr
sReal name = liftIO $ do
  sym <- Z3.mkStringSymbol _globalContext name
  RealExpr <$> Z3.mkRealVar _globalContext sym

laplaceSymbolic :: MonadIO m => RealExpr -> Double -> m RealExpr
laplaceSymbolic c w = liftIO $
  RealExpr <$> Z3.mkFreshRealVar _globalContext "lap"

gaussianSymbolic :: MonadIO m => RealExpr -> Double -> m RealExpr
gaussianSymbolic c w = liftIO $
  RealExpr <$> Z3.mkFreshRealVar _globalContext "gauss"

instance Num RealExpr where
  (RealExpr a) + (RealExpr b) = unsafePerformIO $ do
    s <- Z3.mkAdd _globalContext [a,b]
    return (RealExpr s)
  (RealExpr a) - (RealExpr b) = unsafePerformIO $ do
    s <- Z3.mkSub _globalContext [a,b]
    return (RealExpr s)
  (RealExpr a) * (RealExpr b) = unsafePerformIO $ do
    s <- Z3.mkMul _globalContext [a,b]
    return (RealExpr s)
  abs (RealExpr a) = unsafePerformIO $ do
    zero <- Z3.mkIntegral _globalContext 0 _realSort
    cond <- Z3.mkGe _globalContext a zero
    negA <- Z3.mkSub _globalContext [zero, a]
    -- if a >= 0 then a else -a
    expr <- Z3.mkIte _globalContext cond a negA
    return (RealExpr expr)
  signum (RealExpr a) = unsafePerformIO $ do
    zero <- Z3.mkIntegral _globalContext 0 _realSort
    one  <- Z3.mkIntegral _globalContext 1 _realSort
    negOne <- Z3.mkIntegral _globalContext (-1) _realSort
    condZero <- Z3.mkEq _globalContext a zero
    condGt   <- Z3.mkGt _globalContext a zero
    -- if a == 0 then 0 else (if a > 0 then 1 else -1)
    subExpr <- Z3.mkIte _globalContext condGt one negOne
    expr <- Z3.mkIte _globalContext condZero zero subExpr
    return (RealExpr expr)
  fromInteger v = unsafePerformIO $ do
    a <- Z3.mkIntegral _globalContext v _realSort
    return (RealExpr a)

instance Fractional RealExpr where
  (RealExpr a) / (RealExpr b) = unsafePerformIO $ do
    s <- Z3.mkDiv _globalContext a b
    return (RealExpr s)
  fromRational v = unsafePerformIO $ do
    s <- Z3.mkRational _globalContext v
    return (RealExpr s)

instance Boolean BoolExpr where
  and (BoolExpr a) (BoolExpr b) = unsafePerformIO $ do
    ab <- Z3.mkAnd _globalContext [a,b]
    return (BoolExpr ab)
  or (BoolExpr a) (BoolExpr b) = unsafePerformIO $ do
    ab <- Z3.mkOr _globalContext [a,b]
    return (BoolExpr ab)
  neg (BoolExpr a) = unsafePerformIO $ do
    notA <- Z3.mkNot _globalContext a
    return (BoolExpr notA)

instance Ordered RealExpr where
  type CmpResult RealExpr = BoolExpr
  (RealExpr a) %< (RealExpr b) = unsafePerformIO $ do
    ab <- Z3.mkLt _globalContext a b
    return (BoolExpr ab)
  (RealExpr a) %<= (RealExpr b) = unsafePerformIO $ do
    ab <- Z3.mkLe _globalContext a b
    return (BoolExpr ab)
  (RealExpr a) %> (RealExpr b) = unsafePerformIO $ do
    ab <- Z3.mkGt _globalContext a b
    return (BoolExpr ab)
  (RealExpr a) %>= (RealExpr b) = unsafePerformIO $ do
    ab <- Z3.mkGe _globalContext a b
    return (BoolExpr ab)
  (RealExpr a) %== (RealExpr b) = unsafePerformIO $ do
    ab <- Z3.mkEq _globalContext a b
    return (BoolExpr ab)
  a %/= b = neg (a %== b)

instance Numeric     RealExpr
instance FracNumeric RealExpr
