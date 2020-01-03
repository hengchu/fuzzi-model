module Data.Fuzzi.Extraction.Python3 where

import Control.Lens hiding (List)
import Control.Monad.Except
import Control.Monad.Reader hiding (local)
import Control.Monad.State.Strict
import Data.Fuzzi.Distribution()
import Data.Fuzzi.EDSL
import Data.Fuzzi.IfCxt
import Data.Fuzzi.Types hiding (And, Or, Not, Add, Sub, Div)
import Data.Maybe
import Data.Proxy
import Prelude hiding ((<>), LT)
import Text.PrettyPrint
import Type.Reflection hiding (App)
import qualified Data.Map.Strict as M

--data IndentChar = Space | Tab
--  deriving (Show, Eq, Ord)

data Bop = Add  | Mult
         | Sub  | Div
         | IDiv | IMod
         | Lt   | Le | Gt | Ge
         | Eq_  | Neq
         | Conj | Disj
  deriving (Show, Eq, Ord)

bop2str :: Bop -> String
bop2str Data.Fuzzi.Extraction.Python3.Add = "+"
bop2str Data.Fuzzi.Extraction.Python3.Mult = "*"
bop2str Data.Fuzzi.Extraction.Python3.Sub = "-"
bop2str Data.Fuzzi.Extraction.Python3.Div = "/"
bop2str Data.Fuzzi.Extraction.Python3.IDiv = "//"
bop2str Data.Fuzzi.Extraction.Python3.IMod = "%"
bop2str Data.Fuzzi.Extraction.Python3.Lt = "<"
bop2str Data.Fuzzi.Extraction.Python3.Le = "<="
bop2str Data.Fuzzi.Extraction.Python3.Gt = ">"
bop2str Data.Fuzzi.Extraction.Python3.Ge = ">="
bop2str Data.Fuzzi.Extraction.Python3.Eq_ = "=="
bop2str Data.Fuzzi.Extraction.Python3.Neq = "!="
bop2str Data.Fuzzi.Extraction.Python3.Conj = "and"
bop2str Data.Fuzzi.Extraction.Python3.Disj = "or"

data Uop = BNot
  deriving (Show, Eq, Ord)

-- |All operators associate left to right
precTable :: M.Map String Int
precTable = fmap (*100) $ M.fromList [("list", 10), ("slice", 10), ("tuple", 10),
                                      ("index", 9), ("call", 9),
                                      ("neg", 8),
                                      ("*", 7), ("/", 7), ("//", 7), ("%", 7),
                                      ("+", 6), ("-", 6),
                                      ("<", 5), ("<=", 5), (">", 5), (">=", 5), ("!=", 5), ("==", 5),
                                      ("not", 4),
                                      ("and", 3),
                                      ("or", 2)
                                     ]

data Exp = Binary Exp Bop Exp
         | List [Exp]
         | Tuple [Exp]
         | Index Exp Exp
         | Slice Exp (Maybe Exp) (Maybe Exp)
         | Unary Uop Exp
         | Call Exp [Exp]
         | Var String
         | Val IR
         | None
  deriving (Show, Eq, Ord)

data Stmt = ExpStmt Exp
          | Assign  String Exp
          | Assert  Exp
          | Cond    Exp    [Stmt] [Stmt]
          | While   Exp    [Stmt]
          | Ret     Exp
          | Decl    FuncDecl
          | Skip
  deriving (Show, Eq, Ord)

data FuncDecl = FuncDecl {
  _fdName     :: String
  , _fdParams :: [String]
  , _fdBody   :: [Stmt]
  }
  deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''FuncDecl

data ExtractionOptions = ExtractionOptions {
  _eoIndentLevel :: Int
  , _eoFunctionName :: String
  , _eoFunctionParams :: [String]
  }

makeLensesWith abbreviatedFields ''ExtractionOptions

defaultExtractionOptions :: ExtractionOptions
defaultExtractionOptions = ExtractionOptions 2 "fuzzi_fun" []

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

emptyExtractionState :: [String] -> ExtractionState
emptyExtractionState functionParams =
  ExtractionState M.empty [M.fromList $ map (\x -> (x,1)) functionParams]

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

extractPython3Default :: Fuzzi a -> Either ExtractionError Doc
extractPython3Default = extractPython3 defaultExtractionOptions

extractPython3 :: ExtractionOptions -> Fuzzi a -> Either ExtractionError Doc
extractPython3 opts prog =
  evalStateT (runReaderT (extractDoc' prog) opts) (emptyExtractionState $ opts ^. functionParams)

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
      return (aStmts ++ bStmts, Just $ Binary aExp op bExp)
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
extract' (Not a) = do
  (aStmts, aExp) <- extract' a
  return (aStmts, fmap (Unary BNot) aExp)
extract' (Data.Fuzzi.EDSL.Add a b) =
  extractBinop' "Add" Data.Fuzzi.Extraction.Python3.Add a b
extract' (Data.Fuzzi.EDSL.Mult a b) =
  extractBinop' "Mult" Data.Fuzzi.Extraction.Python3.Mult a b
extract' (Data.Fuzzi.EDSL.Div a b) =
  extractBinop' "Div" Data.Fuzzi.Extraction.Python3.Div a b
extract' (Data.Fuzzi.EDSL.Sub a b) =
  extractBinop' "Sub" Data.Fuzzi.Extraction.Python3.Sub a b
extract' (Data.Fuzzi.EDSL.Sign a) = do
  (aStmts, aExp) <- extract' a
  let signFunc = Var "np.sign"
  return (aStmts, fmap (\x -> Call signFunc [x]) aExp)
extract' (Data.Fuzzi.EDSL.Abs a) = do
  (aStmts, aExp) <- extract' a
  let absFunc = Var "np.abs"
  return (aStmts, fmap (\x -> Call absFunc [x]) aExp)
extract' (Data.Fuzzi.EDSL.IDiv a b) = do
  extractBinop' "IDiv" Data.Fuzzi.Extraction.Python3.IDiv a b
extract' (Data.Fuzzi.EDSL.IMod a b) = do
  extractBinop' "IMod" Data.Fuzzi.Extraction.Python3.IMod a b
extract' (FExp a) = do
  (aStmts, aExp) <- extract' a
  let expFunc = Var "np.exp"
  return (aStmts, fmap (\x -> Call expFunc [x]) aExp)
extract' (Data.Fuzzi.EDSL.Lt a b) = do
  extractBinop' "Lt" Data.Fuzzi.Extraction.Python3.Lt a b
extract' (Data.Fuzzi.EDSL.Le a b) = do
  extractBinop' "Le" Data.Fuzzi.Extraction.Python3.Le a b
extract' (Data.Fuzzi.EDSL.Gt a b) = do
  extractBinop' "Gt" Data.Fuzzi.Extraction.Python3.Gt a b
extract' (Data.Fuzzi.EDSL.Ge a b) = do
  extractBinop' "Ge" Data.Fuzzi.Extraction.Python3.Ge a b
extract' (Data.Fuzzi.EDSL.Eq_ a b) = do
  extractBinop' "Eq_" Data.Fuzzi.Extraction.Python3.Eq_ a b
extract' (Data.Fuzzi.EDSL.Neq a b) = do
  extractBinop' "Neq" Data.Fuzzi.Extraction.Python3.Neq a b
extract' (Data.Fuzzi.EDSL.AssertTrueM cond) = do
  (condStmts, condExpr) <- extract' cond
  case condExpr of
    Just condExpr ->
      return (condStmts ++ [Assert condExpr], Nothing)
    Nothing -> throwError
      $ InternalError "AssertTrueM: expect condition to produce expression"
extract' (Data.Fuzzi.EDSL.AssertFalseM cond) = do
  (condStmts, condExpr) <- extract' (Data.Fuzzi.EDSL.Not cond)
  case condExpr of
    Just condExpr ->
      return (condStmts ++ [Assert condExpr], Nothing)
    Nothing -> throwError
      $ InternalError "AssertFalseM: expect condition to produce expression"
extract' ListNil =
  return ([], Just . Val $ LT [])
extract' (ListCons x xs) = do
  (xStmts,  xExpr)  <- extract' x
  (xsStmts, xsExpr) <- extract' xs
  case (xExpr, xsExpr) of
    (Just xExpr, Just xsExpr) -> do
      return ( xStmts ++ xsStmts
             , Just $ Binary (List [xExpr]) Data.Fuzzi.Extraction.Python3.Add xsExpr)
    _ -> throwError
      $ InternalError "ListCons: expecting both operands to produce expression"
extract' (ListSnoc xs x) = do
  (xsStmts, xsExpr) <- extract' xs
  (xStmts,  xExpr)  <- extract' x
  case (xsExpr, xExpr) of
    (Just xsExpr, Just xExpr) -> do
      return ( xsStmts ++ xStmts
             , Just $ Binary xsExpr Data.Fuzzi.Extraction.Python3.Add (List [xExpr]))
    _ -> throwError
      $ InternalError "ListSnoc: expecting both operands to produce expression"
extract' (ListIsNil xs) = do
  (xsStmts, xsExpr) <- extract' xs
  return (xsStmts, fmap (Binary (List []) Data.Fuzzi.Extraction.Python3.Eq_) xsExpr)
extract' (ListUncons xs) = do
  (xsStmts, xsExpr) <- extract' xs
  case xsExpr of
    Just xsExpr -> do
      headName <- freshL "uncons_head"
      tailName <- freshL "uncons_tail"
      resultName <- freshL "uncons_result"
      let cond = Cond xsExpr
                   [ Assign headName (Index xsExpr (Val $ IT 0))
                   , Assign tailName (Slice xsExpr (Just $ Val $ IT 1) Nothing)
                   , Assign resultName (Tuple [Var headName, Var tailName])
                   ]
                   [ Assign resultName None ]
      return (xsStmts ++ [cond], Just (Var resultName))
    Nothing -> throwError
      $ InternalError "ListUncons: expecting both operands to produce expression"
extract' (Just_ x) = extract' x
extract' Nothing_ = return ([], Just None)
extract' (IsJust_ x) = do
  (xStmts, xExp) <- extract' x
  case xExp of
    Just xExp -> return (xStmts, Just xExp)
    Nothing -> throwError $ InternalError "IsJust_: expect operand to produce expression"
extract' (FromJust_ x) = do
  (xStmts, xExp) <- extract' x
  case xExp of
    Just xExp -> return (xStmts, Just xExp)
    Nothing -> throwError $ InternalError "FromJust_: expect operand to produce expression"
extract' (Pair a b) = do
  (aStmts, aExpr) <- extract' a
  (bStmts, bExpr) <- extract' b
  case (aExpr, bExpr) of
    (Just aExpr, Just bExpr) ->
      return (aStmts ++ bStmts, Just $ Tuple [aExpr, bExpr])
    _ -> throwError $
      InternalError "Pair: expect both operands to produce expression"
extract' (Fst a) = do
  (aStmts, aExpr) <- extract' a
  return (aStmts, fmap (flip Index (Val (IT 0))) aExpr)
extract' (Snd a) = do
  (aStmts, aExpr) <- extract' a
  return (aStmts, fmap (flip Index (Val (IT 1))) aExpr)
extract' (Abort _reason) =
  throwError $ InternalError "Abort: extraction is not implemented yet"
extract' (UpdatePrivTree _ _ _) =
  throwError $ InternalError "UpdatePrivTree: extraction is not implemented yet"
extract' (Gaussian'{}) =
  throwError $ InternalError "Gaussian': extraction is not implemented yet"
extract' (NumCast a) = do
  (aStmts, aExpr) <- extract' a
  return (aStmts, fmap (\e -> Call (Var "float") [e]) aExpr)
extract' (Loop acc pred iter) = do
  (accStmts, accExp) <- extract' acc
  case accExp of
    Just accExp -> do
      accName <- freshL "loop_acc"
      let assignAcc = Assign accName accExp
      condName <- freshL "loop_cond"
      (condStmts, condExp) <- extract' (pred (PrettyPrintVariable accName))
      case condExp of
        Just condExp -> do
          let assignCond = Assign condName condExp
          (iterStmts, iterExp) <- extract' (iter (PrettyPrintVariable accName))
          case iterExp of
            Just iterExp -> do
              let reAssignAcc = Assign accName iterExp
              let stmts = accStmts ++ (assignAcc:condStmts ++ [assignCond]) ++ [While (Var condName) (iterStmts ++ [reAssignAcc] ++ condStmts ++ [assignCond])]
              return (stmts, Just (Var accName))
            Nothing ->
              throwError $ InternalError "Loop: expected iterator to produce expression"
        Nothing -> throwError $ InternalError "Loop: expected predicate to produce expression"
    Nothing -> throwError $ InternalError "Loop: expected accumulator to produce expression"

extractTopFuncDecl' :: ( MonadState  ExtractionState   m
                  , MonadReader ExtractionOptions m
                  , MonadError  ExtractionError   m
                  ) => Fuzzi a -> m FuncDecl
extractTopFuncDecl' prog = do
  v <- extract' prog
  topFunName   <- (^. functionName)   <$> ask
  topFunParams <- (^. functionParams) <$> ask
  case v of
    (stmts, Just e)  ->
      return $ FuncDecl topFunName topFunParams $ stmts ++ [Ret e]
    (stmts, Nothing) ->
      return $ FuncDecl topFunName topFunParams $ if length stmts == 0 then [Skip] else stmts

extractDoc' :: ( MonadState  ExtractionState   m
               , MonadReader ExtractionOptions m
               , MonadError  ExtractionError   m
               ) => Fuzzi a -> m Doc
extractDoc' prog = do
  fDecl <- extractTopFuncDecl' prog
  indentLvl <- (^. indentLevel) <$> ask
  return $ prettyStmt indentLvl (Decl fDecl)

prettyExp :: Int -> Exp -> Doc
prettyExp prec (Binary e1 op e2) =
  let opStr = bop2str op
      opPrec = precTable M.! opStr
      e1' = prettyExp opPrec e1
      e2' = prettyExp (opPrec + 1) e2
  in parensIf (prec > opPrec) $ e1' <+> text opStr <+> e2'
prettyExp prec (List es) =
  let es' = map (prettyExp 0) es
  in parensIf (prec > precTable M.! "list") $ brackets $ hsep $ punctuate comma es'
prettyExp _ (Tuple es) =
  let es' = map (prettyExp 0) es
  in parens $ hsep $ punctuate comma es'
prettyExp prec (Index e eidx) =
  let indexPrec = precTable M.! "index"
      e' = prettyExp indexPrec e
      eidx' = prettyExp 0 eidx
  in parensIf (prec > indexPrec) $ e' <> brackets eidx'
prettyExp prec (Slice e start end) =
  let slicePrec = precTable M.! "slice"
      e' = prettyExp slicePrec e
      start' = fromMaybe empty $ fmap (prettyExp 0) start
      end'   = fromMaybe empty $ fmap (prettyExp 0) end
  in parensIf (prec > slicePrec) $ e' <> (brackets (start' <> colon <> end'))
prettyExp prec (Unary BNot e) =
  let notPrec = precTable M.! "not"
      e' = prettyExp notPrec e
  in parensIf (prec > notPrec) $ text "not" <+> e'
prettyExp prec (Call e es) =
  let callPrec = precTable M.! "call"
      e' = prettyExp callPrec e
      es' = map (prettyExp 0) es
  in parensIf (callPrec > prec) $ e' <> (parens $ hsep $ punctuate comma es')
prettyExp _ (Var x) = text x
prettyExp prec (Val ir) = prettyIR prec ir
prettyExp _ None = text "None"

prettyIR :: Int -> IR -> Doc
prettyIR _    (DB d) = Text.PrettyPrint.double d
prettyIR _    (IT i) = Text.PrettyPrint.integer i
prettyIR prec (LT irs) =
  let irs' = map (prettyIR 0) irs
  in parensIf (prec > precTable M.! "list") $ brackets $ hsep $ punctuate comma irs'
prettyIR prec (MP (M.toList -> kvs)) =
  let kvs'= fmap (bimap (prettyIR 0) (prettyIR 0)) kvs :: [(Doc, Doc)]
  in parensIf (prec > precTable M.! "dict") $ braces $ hsep $ punctuate comma (formatKVs kvs')
  where formatKVs []           = []
        formatKVs ((k,v):more) = (k <> colon <+> v):(formatKVs more)

prettyStmt :: Int -> Stmt -> Doc
prettyStmt _   (ExpStmt e)  = prettyExp 0 e
prettyStmt _   (Assign x e) = text x <+> equals <+> prettyExp 0 e
prettyStmt _   (Assert e) = text "assert" <+> prettyExp 0 e
prettyStmt lvl (Cond e stmts1 stmts2) =
  let e'      = prettyExp 0 e
      stmts1' = if length stmts1 == 0 then text "skip" else vcat $ map (prettyStmt lvl) stmts1
      stmts2' = if length stmts2 == 0 then text "skip" else vcat $ map (prettyStmt lvl) stmts2
  in vcat [ text "if" <+> e' <> colon
          , nest lvl stmts1'
          , text "else" <> colon
          , nest lvl stmts2'
          ]
prettyStmt _   (Ret e) =
  text "return" <+> prettyExp 0 e
prettyStmt lvl (Decl (FuncDecl name paramNames stmts)) =
  let stmts' = vcat $ map (prettyStmt lvl) stmts
  in vcat [ text "def" <+> text name <> (parens $ hsep $ punctuate comma (map text paramNames)) <> colon
          , nest lvl stmts'
          , text "\n"
          ]
prettyStmt lvl (While cond stmts) =
  let stmts' = if length stmts == 0 then text "skip" else vcat $ map (prettyStmt lvl) stmts
  in vcat [ text "while" <+> prettyExp 0 cond <> colon
          , nest lvl stmts'
          ]
prettyStmt _   Skip = text "skip"

commaSpace :: Doc
commaSpace = comma <+> space
