{-# OPTIONS_HADDOCK hide #-}
module Data.Fuzzi.Z3 where

--import Control.Monad
import Control.Monad.IO.Class
--import Control.Monad.Reader.Class
--import Control.Monad.Trans.Reader hiding (ask)
import Data.Fuzzi.Logging
import Data.Fuzzi.Types
import qualified Data.Map.Strict as M
import qualified Z3.Base as Z3

z3Init :: (MonadIO m, MonadLogger m) => m (Z3.Context, Z3.Solver)
z3Init = do
  cfg <- liftIO Z3.mkConfig
  ctx <- liftIO (Z3.mkContext cfg)
  liftIO (Z3.setASTPrintMode ctx Z3.Z3_PRINT_SMTLIB2_COMPLIANT)
  solver <- liftIO (Z3.mkSolver ctx)-- Z3.QF_NRA)
  $(logDebug) "initialized Z3 solver and context"
  return (ctx, solver)

z3InitOpt :: (MonadIO m, MonadLogger m) => m (Z3.Context, Z3.Optimizer)
z3InitOpt = do
  cfg <- liftIO Z3.mkConfig
  ctx <- liftIO (Z3.mkContext cfg)
  liftIO (Z3.setASTPrintMode ctx Z3.Z3_PRINT_SMTLIB2_COMPLIANT)
  optimizer <- liftIO (Z3.mkOptimizer ctx)
  $(logInfo) "initialized Z3 optimizer and context"
  return (ctx, optimizer)

type AllocatedArrays = M.Map String ()

symbolicExprToZ3AST :: MonadIO m => Z3.Context -> SymbolicExpr -> m Z3.AST
symbolicExprToZ3AST ctx (BoolVar name) = do
  sym <- liftIO (Z3.mkStringSymbol ctx name)
  liftIO (Z3.mkBoolVar ctx sym)
symbolicExprToZ3AST ctx (RealVar name) = do
  sym <- liftIO (Z3.mkStringSymbol ctx name)
  liftIO (Z3.mkRealVar ctx sym)
symbolicExprToZ3AST ctx (IntVar name) = do
  sym <- liftIO (Z3.mkStringSymbol ctx name)
  liftIO (Z3.mkIntVar ctx sym)
{-
symbolicExprToZ3AST _ (RealArrayVar name) =
  error $ "symbolicExprToZ3AST: found free-standing real array variable " ++ name ++ "\n"
          ++ "arrays should always appear in an indexed expression"
-}
symbolicExprToZ3AST ctx (JustInt v) =
  liftIO (Z3.mkInteger ctx v)
symbolicExprToZ3AST ctx (Rat v) =
  liftIO (Z3.mkRational ctx v)
symbolicExprToZ3AST ctx (JustBool v) =
  liftIO (Z3.mkBool ctx v)
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
symbolicExprToZ3AST ctx (Imply a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkImplies ctx a' b')
symbolicExprToZ3AST ctx (Not a) = do
  a' <- symbolicExprToZ3AST ctx a
  liftIO (Z3.mkNot ctx a')
symbolicExprToZ3AST ctx (Ite a b c) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  c' <- symbolicExprToZ3AST ctx c
  liftIO (Z3.mkIte ctx a' b' c')
{-
symbolicExprToZ3AST ctx (RealArrayIndex (RealArrayVar x) idx) = do
  arrayDecls <- ask
  case M.lookup x arrayDecls of
    Nothing -> error $ "symbolicExprToZ3AST: unknown array " ++ x
    Just decl -> do
      idxAst <- symbolicExprToZ3AST ctx idx
      liftIO $ Z3.mkApp ctx decl [idxAst]
symbolicExprToZ3AST _ e@(RealArrayIndex _ _) =
  error $ "symbolicExprToZ3AST: unsupported array indexing in expression " ++ show e
-}
symbolicExprToZ3AST ctx (Int2Real e) = do
  intE <- symbolicExprToZ3AST ctx e
  liftIO $ Z3.mkInt2Real ctx intE
symbolicExprToZ3AST ctx (Substitute a fts) = do
  let f (from, to) = do
        fromSym <- liftIO $ Z3.mkStringSymbol ctx from
        from' <- liftIO $ Z3.mkRealVar ctx fromSym
        to'   <- symbolicExprToZ3AST ctx to
        return (from', to')
  a'   <- symbolicExprToZ3AST ctx a
  fts' <- mapM f fts
  liftIO (Z3.substitute ctx a' fts')
