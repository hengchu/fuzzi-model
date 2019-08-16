module Symbol where

{- HLINT ignore "Use newtype instead of data" -}

import Types
import Control.Monad.IO.Class
import Control.Monad.State.Class
import Control.Monad.Trans.State hiding (gets, put, modify)
import Control.Monad.Trans.Class
import qualified Data.Map.Strict as M
import qualified Z3.Base as Z3
import Data.Coerce
import Data.Foldable

data SymbolicExpr :: * where
  RealVar :: String -> SymbolicExpr

  Rat :: Rational     -> SymbolicExpr

  Add :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Sub :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Mul :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Div :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr

  Lt  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Le  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Gt  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Ge  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Eq_ :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr

  And :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Or  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Not :: SymbolicExpr -> SymbolicExpr

  Ite :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  deriving (Show, Eq, Ord)

newtype RealExpr = RealExpr { getRealExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord)

newtype BoolExpr = BoolExpr { getBoolExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord)

type NameMap = M.Map String Int
data SymbolicState = SymbolicState {
  nameMap :: NameMap
  , assertions :: [BoolExpr]
  } deriving (Show, Eq, Ord)

newtype SymbolicT m a = SymbolicT { runSymbolicT_ :: StateT SymbolicState m a }
  deriving (MonadTrans)         via (StateT SymbolicState)
  deriving (MonadState SymbolicState) via (StateT SymbolicState m)
  deriving (Functor, Applicative, Monad) via (StateT SymbolicState m)

z3Init :: (MonadIO m) => m (Z3.Context, Z3.Solver)
z3Init = do
  cfg <- liftIO Z3.mkConfig
  ctx <- liftIO (Z3.mkContext cfg)
  solver <- liftIO (Z3.mkSolver ctx)
  return (ctx, solver)

symbolicExprToZ3AST :: (MonadIO m) => Z3.Context -> SymbolicExpr -> m Z3.AST
symbolicExprToZ3AST ctx (RealVar name) = do
  realSort <- liftIO (Z3.mkRealSort ctx)
  sym <- liftIO (Z3.mkStringSymbol ctx name)
  liftIO (Z3.mkRealVar ctx sym)
symbolicExprToZ3AST ctx (Rat v) =
  liftIO (Z3.mkRational ctx v)
symbolicExprToZ3AST ctx (Add a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkAdd ctx [a', b'])
symbolicExprToZ3AST ctx (Sub a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkSub ctx [a', b'])
symbolicExprToZ3AST ctx (Mul a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkMul ctx [a', b'])
symbolicExprToZ3AST ctx (Div a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkDiv ctx a' b')
symbolicExprToZ3AST ctx (Lt a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkLt ctx a' b')
symbolicExprToZ3AST ctx (Le a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkLe ctx a' b')
symbolicExprToZ3AST ctx (Gt a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkGt ctx a' b')
symbolicExprToZ3AST ctx (Ge a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkGe ctx a' b')
symbolicExprToZ3AST ctx (Eq_ a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkEq ctx a' b')
symbolicExprToZ3AST ctx (And a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkAnd ctx [a', b'])
symbolicExprToZ3AST ctx (Or a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkOr ctx [a', b'])
symbolicExprToZ3AST ctx (Not a) = do
  a' <- symbolicExprToZ3AST ctx a
  liftIO (Z3.mkNot ctx a')
symbolicExprToZ3AST ctx (Ite a b c) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  c' <- symbolicExprToZ3AST ctx c
  liftIO (Z3.mkIte ctx a' b' c')

runSymbolicT :: (MonadIO m) => SymbolicT m a -> m (a, Z3.Result)
runSymbolicT (SymbolicT m) = do
  (a, symbolicSt :: SymbolicState) <- runStateT m (SymbolicState M.empty [])
  (ctx, solver) <- z3Init
  for_ (assertions symbolicSt) $ \boolExpr -> do
    clause <- symbolicExprToZ3AST ctx (getBoolExpr boolExpr)
    liftIO $ Z3.solverAssertCnstr ctx solver clause
  result <- liftIO $ Z3.solverCheck ctx solver
  return (a, result)

sReal :: String -> RealExpr
sReal = RealExpr . RealVar

freshSReal :: (Monad m) => String -> SymbolicT m RealExpr
freshSReal name = do
  maybeCounter <- gets (M.lookup name . nameMap)
  case maybeCounter of
    Just c -> do
      modify (\st -> st{nameMap = M.adjust (+1) name (nameMap st)})
      return (sReal $ name ++ show c)
    Nothing -> do
      modify (\st -> st{nameMap = M.insert name 1 (nameMap st)})
      return (sReal name)

laplaceSymbolic :: (Monad m) => RealExpr -> Double -> SymbolicT m RealExpr
laplaceSymbolic _ _ = freshSReal "lap"

gaussianSymbolic :: (Monad m) => RealExpr -> Double -> SymbolicT m RealExpr
gaussianSymbolic _ _ = freshSReal "gauss"

assert :: (Monad m) => BoolExpr -> SymbolicT m ()
assert cond = modify (\st -> st{assertions=(assertions st ++ [cond])})

instance Num RealExpr where
  (+) = coerce Add
  (-) = coerce Sub
  (*) = coerce Mul
  abs (RealExpr ast) =
    let geZero = ast `Ge` (Rat 0)
        negAst = (Rat 0) `Sub` ast
    in RealExpr $ Ite geZero ast negAst
  signum (RealExpr ast) =
    let eqZero = ast `Eq_` (Rat 0)
        gtZero = ast `Gt` (Rat 0)
    in RealExpr $ Ite eqZero (Rat 0) (Ite gtZero (Rat 1) (Rat (-1)))
  fromInteger v = RealExpr $ Rat (fromInteger v)

instance Fractional RealExpr where
  (/) = coerce Div
  fromRational = RealExpr . Rat

instance Boolean BoolExpr where
  and = coerce And
  or  = coerce Or
  neg = coerce Not

instance Ordered RealExpr where
  type CmpResult RealExpr = BoolExpr

  (%<) = coerce Lt
  (%<=) = coerce Le
  (%>) = coerce Gt
  (%>=) = coerce Ge
  (%==) = coerce Eq_
  a %/= b = neg (a %== b)

instance Numeric     RealExpr
instance FracNumeric RealExpr
