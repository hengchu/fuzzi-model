module Data.Fuzzi.Types.SymbolicExpr where

import Data.Text (Text)
import Data.Bifunctor
import qualified Text.PrettyPrint as TPP
import qualified Data.Map.Strict as M
import Data.Coerce
import Data.Hashable
import GHC.Generics
import Control.DeepSeq

data SymbolicExpr :: * where
  BoolVar :: String -> SymbolicExpr
  RealVar :: String -> SymbolicExpr
  --RealArrayVar :: String -> SymbolicExpr

  JustInt  :: Integer  -> SymbolicExpr
  Rat      :: Rational -> SymbolicExpr
  JustBool :: Bool     -> SymbolicExpr

  Add :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Sub :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Mul :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Div :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr

  Lt  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Le  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Gt  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Ge  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Eq_ :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr

  And   :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Or    :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Imply :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Not   :: SymbolicExpr -> SymbolicExpr

  -- RealArrayIndex :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr

  Ite :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr

  Substitute :: SymbolicExpr -> [(String, SymbolicExpr)] -> SymbolicExpr
  deriving (Eq, Ord, Generic)

instance NFData SymbolicExpr

int :: Integer -> IntExpr
int = IntExpr . JustInt

double :: Double -> RealExpr
double = fromRational . toRational

bool :: Bool -> BoolExpr
bool = BoolExpr . JustBool

beq :: BoolExpr -> BoolExpr -> BoolExpr
beq (BoolExpr b1) (BoolExpr b2) = BoolExpr (Eq_ b1 b2)

imply :: BoolExpr -> BoolExpr -> BoolExpr
imply = coerce Imply

newtype ArrayExpr = ArrayExpr { getArrayExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord, Generic)

newtype IntExpr = IntExpr { getIntExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord, Generic)

data RealExpr = RealExpr { getTolerance :: Rational
                         , getRealExpr :: SymbolicExpr
                         }
  deriving (Eq, Ord, Generic)

newtype BoolExpr = BoolExpr { getBoolExpr :: SymbolicExpr }
  deriving (Eq, Ord, Generic)
  deriving (Hashable) via SymbolicExpr

instance NFData BoolExpr
instance NFData RealExpr
instance NFData IntExpr
instance NFData ArrayExpr

instance Show RealExpr where
  show a = show (getRealExpr a)

instance Show BoolExpr where
  show a = show (getBoolExpr a)

instance Num RealExpr where
  RealExpr tol left + RealExpr tol' right = RealExpr (max tol tol') (Add left right)
  RealExpr tol left - RealExpr tol' right = RealExpr (max tol tol') (Sub left right)
  RealExpr tol left * RealExpr tol' right = RealExpr (max tol tol') (Mul left right)
  abs (RealExpr tol ast) =
    let geZero = ast `Ge` Rat 0
        negAst = Rat 0 `Sub` ast
    in RealExpr tol $ Ite geZero ast negAst
  signum (RealExpr tol ast) =
    let eqZero = ast `Eq_` Rat 0
        gtZero = ast `Gt` Rat 0
    in RealExpr tol $ Ite eqZero (Rat 0) (Ite gtZero (Rat 1) (Rat (-1)))
  fromInteger v = RealExpr 0 $ Rat (fromInteger v)

instance Num IntExpr where
  (+) = coerce Add
  (-) = coerce Sub
  (*) = coerce Mul
  negate v = IntExpr $ Rat 0 `Sub` getIntExpr v
  abs (IntExpr ast) =
    let geZero = ast `Ge` Rat 0
        negAst = Rat 0 `Sub` ast
    in IntExpr $ Ite geZero ast negAst
  signum (IntExpr ast) =
    let eqZero = ast `Eq_` Rat 0
        gtZero = ast `Gt` Rat 0
    in IntExpr $ Ite eqZero (Rat 0) (Ite gtZero (Rat 1) (Rat (-1)))
  fromInteger = IntExpr . JustInt

instance Fractional RealExpr where
  RealExpr tol left / RealExpr tol' right = RealExpr (max tol tol') (Div left right)
  fromRational = RealExpr 0 . Rat

instance Show SymbolicExpr where
  showsPrec prec expr = showParen (prec > 10) $
    showString (pretty expr)

pretty :: SymbolicExpr -> String
pretty = TPP.render . prettySymbolic 0

parensIf :: Bool -> TPP.Doc -> TPP.Doc
parensIf True  = TPP.parens
parensIf False = id

prettySymbolic :: Int -> SymbolicExpr -> TPP.Doc
prettySymbolic _ (BoolVar x) = TPP.text x
prettySymbolic _ (RealVar x) = TPP.text x
--prettySymbolic _ (RealArrayVar x) = TPP.text x
prettySymbolic _ (Rat r) = TPP.text (show r) --TPP.double (fromRational r)
prettySymbolic _ (JustInt i) = TPP.text (show i)
prettySymbolic _ (JustBool b) = TPP.text (show b)
prettySymbolic currPrec (Add x y) =
  let thisPrec = precedence M.! "+" in
  let thisFixity = fixity M.! "+" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "+"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Sub x y) =
  let thisPrec = precedence M.! "-" in
  let thisFixity = fixity M.! "-" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "-"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Mul x y) =
  let thisPrec = precedence M.! "*" in
  let thisFixity = fixity M.! "*" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "*"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Div x y) =
  let thisPrec = precedence M.! "/" in
  let thisFixity = fixity M.! "/" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "/"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Lt x y) =
  let thisPrec = precedence M.! "<" in
  let thisFixity = fixity M.! "<" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "<"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Le x y) =
  let thisPrec = precedence M.! "<=" in
  let thisFixity = fixity M.! "<=" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "<="
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Gt x y) =
  let thisPrec = precedence M.! ">" in
  let thisFixity = fixity M.! ">" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text ">"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Ge x y) =
  let thisPrec = precedence M.! ">=" in
  let thisFixity = fixity M.! ">=" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text ">="
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Eq_ x y) =
  let thisPrec = precedence M.! "==" in
  let thisFixity = fixity M.! "==" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "=="
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (And x y) =
  let thisPrec = precedence M.! "&&" in
  let thisFixity = fixity M.! "&&" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "&&"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Or x y) =
  let thisPrec = precedence M.! "||" in
  let thisFixity = fixity M.! "||" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "||"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Imply x y) =
  let thisPrec = precedence M.! "==>" in
  let thisFixity = fixity M.! "==>" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "==>"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic _ (Not x) =
  TPP.text "not" TPP.<> TPP.parens (prettySymbolic 0 x)
prettySymbolic _ (Ite (e1 `Ge` Rat 0) e2 (Rat 0 `Sub` e3)) -- an optimization for our encoding of absolute values
  | e1 == e2 && e2 == e3 =
    TPP.text "abs" TPP.<> TPP.parens prettyExpr
  where prettyExpr = prettySymbolic 0 e1
prettySymbolic _ (Ite cond x y) =
  TPP.text "ite" TPP.<> TPP.parens (prettyCond `commaSep`
                                    prettyX    `commaSep`
                                    prettyY)
  where prettyX    = prettySymbolic 0 x
        prettyY    = prettySymbolic 0 y
        prettyCond = prettySymbolic 0 cond
-- prettySymbolic currPrec (RealArrayIndex arr idx) =
--   let prec = precedence M.! "index"
--   in parensIf (currPrec > prec)
--        $ prettySymbolic (precedence M.! "index") arr
--          TPP.<> TPP.brackets (prettySymbolic 0 idx)
prettySymbolic _ (Substitute x substs) =
  TPP.text "subst" TPP.<> TPP.parens (prettyX `commaSep`
                                      prettySubsts3)
  where prettyX       = prettySymbolic 0 x
        prettySubsts1 = map (first TPP.text . second (prettySymbolic 0)) substs
        prettySubsts2 =
          foldr (\(f,t) acc -> TPP.parens (f `commaSep` t) `commaSep` acc)
                TPP.empty
                prettySubsts1
        prettySubsts3 = TPP.brackets prettySubsts2

precedence :: M.Map Text Int
precedence = M.fromList [("||", 0), ("&&", 1),
                         ("==", 2),
                         ("<", 3), ("<=", 3), (">", 3), (">=", 3),
                         ("+", 4), ("-", 4),
                         ("*", 5), ("/", 5),
                         ("index", 1000000), -- array index
                         ("app", 1000000), -- function application
                         ("==>", 0)
                        ]

fixity :: M.Map Text Int
fixity = M.fromList [("||", 1),
                     ("&&", 1),
                     ("==", 0),
                     ("<", 0), ("<=", 0),
                     (">", 0), (">=", 0),
                     ("+", 1), ("-", 1),
                     ("*", 1), ("/", 1),
                     ("app", 1), -- function application
                     ("==>", -1)
                    ]

commaSep :: TPP.Doc -> TPP.Doc -> TPP.Doc
commaSep a b = a TPP.<> TPP.comma TPP.<+> b

instance Hashable SymbolicExpr
