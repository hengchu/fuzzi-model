module Data.Fuzzi.Extraction.Python3 where

import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader hiding (local)
import Control.Monad.State.Strict
import Data.Fuzzi.EDSL
import Data.Fuzzi.IfCxt
import Data.Fuzzi.Types hiding (And, Or, Not)
import Data.Proxy
import Prelude hiding ((<>))
import Text.PrettyPrint
import Type.Reflection hiding (App)
import qualified Data.Map.Strict as M

data IndentChar = Space | Tab
  deriving (Show, Eq, Ord)

data Bop = Add  | Mult
         | Sub  | Div
         | IDiv | IMod
         | Lt   | Le | Gt | Ge
         | Eq_  | Neq
         | Conj | Disj
  deriving (Show, Eq, Ord)

data Exp = Binop Exp Bop Exp
         | Call Exp [Exp]
         | Var String
         | Val IR
  deriving (Show, Eq, Ord)

data Stmt = ExpStmt Exp
          | Assign  String Exp
          | Cond    Exp    [Stmt] [Stmt]
          | Ret     Exp
          | Decl    FuncDecl
  deriving (Show, Eq, Ord)

data FuncDecl = FuncDecl {
  _fdName     :: String
  , _fdParams :: [String]
  , _fdBody   :: [Stmt]
  }
  deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''FuncDecl

data ExtractionOptions = ExtractionOptions {
  _eoIndentChar :: IndentChar
  , _eoIndentLevel :: Int
  , _eoFunctionName :: String
  }

type NameMap = M.Map String Int

data ExtractionError = PopEmptyLocalNameStack
                     | FreshEmptyLocalNameStack String
                     | LiteralValueDoesNotImplementToIR String String
                     | UnboundVariable Int
                     | InternalError String
  deriving (Show, Eq, Ord)

data ExtractionState = ExtractionState {
  _esGlobal :: NameMap
  , _esLocal :: [NameMap]
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''ExtractionState

newtype ExtractionM a = ExtractionM {
  runExtractionM :: ReaderT ExtractionOptions
                      (StateT ExtractionState
                         (Either ExtractionError)) a
  } deriving (Functor, Applicative, Monad)
    via (ReaderT ExtractionOptions (StateT ExtractionState (Except ExtractionError)))
    deriving (MonadReader ExtractionOptions)
    via (ReaderT ExtractionOptions (StateT ExtractionState (Except ExtractionError)))
    deriving (MonadState ExtractionState)
    via (ReaderT ExtractionOptions (StateT ExtractionState (Except ExtractionError)))
    deriving (MonadError ExtractionError)
    via (ReaderT ExtractionOptions (StateT ExtractionState (Except ExtractionError)))

freshG :: MonadState ExtractionState m => String -> m String
freshG name = do
  names <- gets (^. global)
  case M.lookup name names of
    Nothing -> do
      modify (\st -> st & global %~ M.insert name 1)
      return name
    Just nextIdx -> do
      modify (\st -> st & global %~ M.insert name (nextIdx + 1))
      return (name ++ show nextIdx)

pushL :: MonadState ExtractionState m => m ()
pushL = do
  localNames <- gets (^. local)
  case localNames of
    []     -> modify (\st -> st & local .~ [M.empty])
    (x:xs) -> modify (\st -> st & local .~ (x:x:xs))

popL :: ( MonadState ExtractionState m
        , MonadError ExtractionError m
        ) => m NameMap
popL = do
  localNames <- gets (^. local)
  case localNames of
    []     -> throwError PopEmptyLocalNameStack
    (x:xs) -> do
      modify (\st -> st & local .~ xs)
      return x

freshL :: ( MonadState ExtractionState m
          , MonadError ExtractionError m
          ) => String -> m String
freshL name = do
  localNames <- gets (^. local)
  case localNames of
    []     -> throwError (FreshEmptyLocalNameStack name)
    (x:xs) -> do
      case M.lookup name x of
        Nothing -> do
          modify (\st -> st & local .~ ((M.insert name 1 x):xs))
          return name
        Just nextIdx -> do
          modify (\st -> st & local .~ ((M.insert name (nextIdx+1) x):xs))
          return (name ++ show nextIdx)

extractBinop' :: ( MonadState ExtractionState m
                 , MonadReader ExtractionOptions m
                 , MonadError ExtractionError m
                 ) => String -> Bop -> Fuzzi a -> Fuzzi a -> m ([Stmt], Maybe Exp)
extractBinop' opName op a b = do
  (aStmts, aExp) <- extract' a
  (bStmts, bExp) <- extract' b
  case (aExp, bExp) of
    (Just aExp, Just bExp) -> do
      return (aStmts ++ bStmts, Just $ Binop aExp op bExp)
    _ -> do
      throwError
        $ InternalError $ opName ++ ": expecting both operands to produce expression"

extractConditional' :: ( MonadState ExtractionState m
                       , MonadReader ExtractionOptions m
                       , MonadError ExtractionError m
                       )
                    => String
                    -> Fuzzi bool
                    -> Fuzzi a
                    -> Fuzzi a
                    -> m ([Stmt], Maybe Exp)
extractConditional' name cond a b = do
  (condStmts, condExp) <- extract' cond
  (aStmts, aExp) <- extract' a
  (bStmts, bExp) <- extract' b
  cond <-
    case condExp of
      Nothing ->
        throwError
          $ InternalError $ name ++ ": expecting condition to produce an expression"
      Just condExp -> return condExp
  case (aExp, bExp) of
    (Just aExp, Nothing) -> do
      aFreshName <- freshL "x"
      let condStmt = Cond cond (aStmts ++ [Assign aFreshName aExp]) bStmts
      return (condStmts ++ [condStmt], Just $ Var aFreshName)
    (Nothing, Just bExp) -> do
      bFreshName <- freshL "x"
      let condStmt = Cond cond aStmts (bStmts ++ [Assign bFreshName bExp])
      return (condStmts ++ [condStmt], Just $ Var bFreshName)
    (Just aExp, Just bExp) -> do
      freshName <- freshL "x"
      let condStmt = Cond cond
                       (aStmts ++ [Assign freshName aExp])
                       (bStmts ++ [Assign freshName bExp])
      return (condStmts ++ [condStmt], Just $ Var freshName)
    (Nothing, Nothing) -> do
      return (condStmts ++ [Cond cond aStmts bStmts], Nothing)

extract' :: ( MonadState ExtractionState m
            , MonadReader ExtractionOptions m
            , MonadError ExtractionError m
            ) => Fuzzi a -> m ([Stmt], Maybe Exp)
extract' (Lam _f)    = throwError $ InternalError "Lam: extraction is not implemented yet"
extract' (App f arg) = do
  (fStmts, fExp)     <- extract' f
  (argStmts, argExp) <- extract' arg
  case (fExp, argExp) of
    (Just fExp, Just argExp) -> return (fStmts ++ argStmts, Just $ Call fExp [argExp])
    _ -> throwError $ InternalError "App: expecting both operands to yield expression"
extract' (Return e)     = extract' e
extract' (Sequence a b) = do
  (aStmts, _)    <- extract' a
  (bStmts, bExp) <- extract' b
  return (aStmts ++ bStmts, bExp)
extract' (Bind a f) = do
  (aStmts, aExp) <- extract' a
  aFreshName <- freshL "x"
  let aParam = PrettyPrintVariable aFreshName
  (fStmts, fExp) <- extract' (f aParam)
  case aExp of
    Just aExp ->
      return (aStmts ++ [Assign aFreshName aExp] ++ fStmts, fExp)
    Nothing ->
      throwError $ InternalError "Bind: expecting bound operand to produce an expression"
extract' (Lit (v :: a)) =
  ifCxt (undefined :: Proxy (ToIR a))
        (return ([], Just $ Val (toIR v)))
        (throwError $ LiteralValueDoesNotImplementToIR (show $ typeRep @a) (show v))
extract' (If cond a b)  = extractConditional' "If" cond a b
extract' (IfM cond a b) = extractConditional' "IfM" cond a b
extract' (Laplace c w) = do
  (cStmts, cExp) <- extract' c
  (wStmts, wExp) <- extract' w
  case (cExp, wExp) of
    (Just cExp, Just wExp) -> do
      return (cStmts ++ wStmts, Just $ Call (Var "laplace_mechanism") [cExp, wExp])
    _ ->
      throwError $ InternalError "Laplace: expecting both center and width to produce expressions"
extract' (Laplace' _ c w) = do
  (cStmts, cExp) <- extract' c
  (wStmts, wExp) <- extract' w
  case (cExp, wExp) of
    (Just cExp, Just wExp) -> do
      return (cStmts ++ wStmts, Just $ Call (Var "laplace_mechanism") [cExp, wExp])
    _ ->
      throwError $ InternalError "Laplace: expecting both center and width to produce expressions"
extract' (Geometric c a) = do
  (cStmts, cExp) <- extract' c
  (aStmts, aExp) <- extract' a
  case (cExp, aExp) of
    (Just cExp, Just aExp) -> do
      return (cStmts ++ aStmts, Just $ Call (Var "geometric_mechanism") [cExp, aExp])
    _ ->
      throwError $ InternalError "Geometric: expecting both center and alpha to produce expressions"
extract' (Gaussian _c _w) =
  throwError $ InternalError "Gaussian: extraction is not implemented yet"
extract' (Variable x) =
  throwError $ UnboundVariable x
extract' (PrettyPrintVariable x) =
  return ([], Just $ Var x)
extract' (And a b) = extractBinop' "And" Conj a b
extract' (Or a b)  = extractBinop' "Or"  Disj a b
