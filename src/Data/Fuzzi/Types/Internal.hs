module Data.Fuzzi.Types.Internal where

import Data.List (find)
import Data.Functor.Compose
import Control.Lens hiding (matching)
import Control.Monad.Catch
import Data.Bifunctor
import Data.Coerce
import Data.Fuzzi.IfCxt
import Data.Maybe
import Data.Text (Text)
import Prelude hiding (and, or)
import Type.Reflection
import qualified Data.Map.Merge.Strict as MM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Prelude
import qualified Text.PrettyPrint as TPP

{- HLINT ignore "Use camelCase" -}

data Guarded (a :: *) where
  MkGuarded :: BoolExpr -> a -> Guarded a
  deriving (Eq, Ord, Functor, Foldable, Traversable)

instance Show a => Show (Guarded a) where
  show (MkGuarded cond v) = "MkGuarded (" ++ show cond ++ ") (" ++ show v ++")"

newtype GuardedSymbolicUnion a =
  GuardedSymbolicUnion { unwrapGuardedSymbolicUnion :: [Guarded a] }
  deriving (Show)
  deriving (Functor, Applicative, Foldable) via (Compose [] Guarded)
  deriving (Traversable)

instance SymbolicRepr a => Eq (GuardedSymbolicUnion a) where
  (GuardedSymbolicUnion a) == (GuardedSymbolicUnion b) =
    S.fromList a == S.fromList b

instance SymbolicRepr a => Ord (GuardedSymbolicUnion a) where
  compare (GuardedSymbolicUnion a) (GuardedSymbolicUnion b) =
    compare (S.fromList a) (S.fromList b)

-- |This constraint is only satisfied by first-class datatypes supported in
-- Fuzzi.
class ( SymbolicRepr a
      , Typeable a
      , Show a
      , Eq a
      , Ord a
      , Matchable a a
      ) => FuzziType (a :: *)

-- |This typeclass is defined for values that have a symbolic representation,
-- and provides a method on how to merge two symbolic values into a union of
-- such values.
class (Matchable a a, Ord a) => SymbolicRepr a where
  merge :: BoolExpr
        -> a
        -> a
        -> GuardedSymbolicUnion a

-- |This typeclass is defined for values that we can establish a symbolic
-- equality condition over.
class Matchable a b => SEq a b where
  symEq :: a -> b -> BoolExpr

-- |Order operators in the semantic domain.
class (Boolean (CmpResult a), Typeable a) => Ordered (a :: *) where
  type CmpResult a :: *
  (%<)  :: a -> a -> CmpResult a
  (%<=) :: a -> a -> CmpResult a
  (%>)  :: a -> a -> CmpResult a
  (%>=) :: a -> a -> CmpResult a
  (%==) :: a -> a -> CmpResult a
  (%/=) :: a -> a -> CmpResult a

class LiteIntegral (a :: *) where
  idiv :: a -> a -> a
  imod :: a -> a -> a

instance LiteIntegral Int where
  idiv = div
  imod = mod

-- |This constraint is only satisfied by numeric datatypes supported in Fuzzi.
class (Ordered a, Num a, Typeable a) => Numeric (a :: *)
class (Numeric a, Fractional a)      => FracNumeric (a :: *)
class (Numeric a, LiteIntegral a)    => IntNumeric (a :: *)

-- |Boolean operators in the semantic domain.
class (Typeable a) => Boolean (a :: *) where
  and :: a -> a -> a
  or  :: a -> a -> a
  neg :: a -> a

class Boolean a => ConcreteBoolean (a :: *) where
  toBool   :: a -> Bool
  fromBool :: Bool -> a

-- |Sample instructions in the semantic domain.
class (Monad m, Typeable m, FracNumeric (NumDomain m)) => MonadDist m where
  type NumDomain m :: *
  laplace   ::             NumDomain m -> Double -> m (NumDomain m)
  laplace'  :: Rational -> NumDomain m -> Double -> m (NumDomain m)
  gaussian  ::             NumDomain m -> Double -> m (NumDomain m)
  gaussian' :: Rational -> NumDomain m -> Double -> m (NumDomain m)

class ( Monad m
      , Typeable m
      , Boolean (BoolType m)
      , MonadThrow m
      , FuzziType (BoolType m)
      ) => MonadAssert m where
  type BoolType m :: *
  assertTrue  :: BoolType m -> m ()
  assertFalse :: BoolType m -> m ()
  assertFalse v = assertTrue (neg v)

class Matchable concrete symbolic where
  match :: concrete -> symbolic -> Bool

type Distribution m a    = (MonadDist m, NumDomain m ~ a, FuzziType a, FracNumeric a)
type Assertion    m bool = (MonadAssert m, BoolType m ~ bool, IfCxt (ConcreteBoolean bool))
type FuzziLang    m a    = (Distribution m a, Assertion m (CmpResult a))

instance Boolean Bool where
  and = (&&)
  or  = (||)
  neg = not

instance ConcreteBoolean Bool where
  toBool   = id
  fromBool = id

instance {-# OVERLAPS #-} IfCxt (ConcreteBoolean Bool) where
  ifCxt _ t _ = t

instance Ordered Double where
  type CmpResult Double = Bool
  (%<)  = (<)
  (%<=) = (<=)
  (%>)  = (>)
  (%>=) = (>=)
  (%==) = (==)
  (%/=) = (/=)

instance Ordered Int where
  type CmpResult Int = Bool
  (%<)  a b = fromBool $ (<) a b
  (%<=) a b = fromBool $ (<=) a b
  (%>)  a b = fromBool $ (>) a b
  (%>=) a b = fromBool $ (>=) a b
  (%==) a b = fromBool $ (==) a b
  (%/=) a b = fromBool $ (/=) a b

data SymbolicExpr :: * where
  RealVar :: String -> SymbolicExpr

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

  And :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Or  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Not :: SymbolicExpr -> SymbolicExpr

  Ite :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr

  Substitute :: SymbolicExpr -> [(String, SymbolicExpr)] -> SymbolicExpr
  deriving (Eq, Ord)

instance Show SymbolicExpr where
  showsPrec prec expr = showParen (prec > 10) $
    showString (pretty expr)

pretty :: SymbolicExpr -> String
pretty = TPP.render . prettySymbolic 0

parensIf :: Bool -> TPP.Doc -> TPP.Doc
parensIf True  = TPP.parens
parensIf False = id

prettySymbolic :: Int -> SymbolicExpr -> TPP.Doc
prettySymbolic _ (RealVar x) = TPP.text x
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

int :: Integer -> IntExpr
int = IntExpr . JustInt

double :: Double -> RealExpr
double = fromRational . toRational

bool :: Bool -> BoolExpr
bool = BoolExpr . JustBool

newtype IntExpr = IntExpr { getIntExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord)

data RealExpr = RealExpr { getTolerance :: Rational
                         , getRealExpr :: SymbolicExpr
                         }
  deriving (Eq, Ord)

instance Show RealExpr where
  show a = show (getRealExpr a)

newtype BoolExpr = BoolExpr { getBoolExpr :: SymbolicExpr }
  deriving (Eq, Ord)

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

instance Boolean BoolExpr where
  -- we only optimize `and` so that condensing symbolic unions do not cause
  -- boolean expression explosion
  and (tryEvalBool -> Just True) b  = b
  and a (tryEvalBool -> Just True)  = a
  and (tryEvalBool -> Just False) _ = bool False
  and _ (tryEvalBool -> Just False) = bool False
  and a b | a == b    = a
          | otherwise = coerce And a b
  or  (tryEvalBool -> Just False) b = b
  or  b (tryEvalBool -> Just False) = b
  or  (tryEvalBool -> Just True) _ = bool True
  or  _ (tryEvalBool -> Just True) = bool True
  or  a b | a == neg b = bool True
          | neg a == b = bool True
          | otherwise = coerce Or a b
  neg = coerce Not

instance Ordered RealExpr where
  type CmpResult RealExpr = BoolExpr

  lhs %< rhs  = BoolExpr (getRealExpr lhs `Lt` getRealExpr rhs)
  lhs %<= rhs = BoolExpr (getRealExpr lhs `Le` getRealExpr rhs)
  lhs %> rhs  = BoolExpr (getRealExpr lhs `Gt` getRealExpr rhs)
  lhs %>= rhs = BoolExpr (getRealExpr lhs `Ge` getRealExpr rhs)
  lhs %== rhs = BoolExpr (getRealExpr lhs `Eq_` getRealExpr rhs)
  a %/= b = neg (a %== b)


instance Numeric Double
instance FracNumeric Double
instance Numeric Int
instance IntNumeric Int

instance Matchable Int Int where
  match a b = a == b

instance Matchable Integer Integer where
  match a b = a == b

instance Matchable Bool Bool where
  match a b = a == b

instance Matchable Double Double where
  match a b = a == b

instance Matchable PrivTreeNode1D PrivTreeNode1D where
  match a b = a == b

instance Matchable Double RealExpr where
  match v sv =
    case tryEvalReal sv of
      Just v' -> toRational v == v'
      Nothing -> True

instance ( Matchable a b
         , Matchable c d
         ) => Matchable (a,c) (b,d) where
  match (a,b) (c,d) = match a c && match b d

instance Matchable a b => Matchable (Maybe a) (Maybe b) where
  match (Just a) (Just b) = match a b
  match Nothing  Nothing  = True
  match _        _        = False

instance Matchable a b => Matchable [a] [b] where
  match []     []     = True
  match (x:xs) (y:ys) = match x y && match xs ys
  match _      _      = False

instance Matchable BoolExpr BoolExpr where
  match _ _ = True

instance Matchable IntExpr  IntExpr where
  match _ _ = True

instance Matchable RealExpr RealExpr where
  match (tryEvalReal -> Just r1) (tryEvalReal -> Just r2) = r1 == r2
  match _                        _                        = True

data PrivTree1DDir = LeftDir | RightDir
  deriving (Show, Eq, Ord)

newtype PrivTreeNode1D = PrivTreeNode1D [PrivTree1DDir]
  deriving (Show, Eq, Ord)

newtype PrivTree1D count = PrivTree1D { getPrivTree1D :: M.Map PrivTreeNode1D count }
  deriving (Show, Eq, Ord)     via (M.Map PrivTreeNode1D count)
  deriving (Functor, Foldable) via (M.Map PrivTreeNode1D)

split :: PrivTreeNode1D -> (PrivTreeNode1D, PrivTreeNode1D)
split (PrivTreeNode1D dirs) = ( PrivTreeNode1D (dirs ++ [LeftDir])
                              , PrivTreeNode1D (dirs ++ [RightDir])
                              )

rootNode :: PrivTreeNode1D
rootNode = PrivTreeNode1D []

emptyTree :: PrivTree1D count
emptyTree = PrivTree1D M.empty

update :: PrivTreeNode1D -> count -> PrivTree1D count -> PrivTree1D count
update k v (PrivTree1D tree) = PrivTree1D $ M.insert k v tree

depth :: (Num count) => PrivTreeNode1D -> count
depth (PrivTreeNode1D dirs) = fromIntegral (length dirs)

endpoints :: PrivTreeNode1D -> (Double, Double)
endpoints (PrivTreeNode1D dirs) = go dirs 0 1
  where go []            start end = (start, end)
        go (LeftDir:xs)  start end = go xs start               ((start + end) / 2)
        go (RightDir:xs) start end = go xs ((start + end) / 2) end

countPoints :: (Num count) => [Double] -> PrivTreeNode1D -> count
countPoints points node =
  fromIntegral $ length (filter (\x -> leftEnd <= x && x < rightEnd) points)
  where (leftEnd, rightEnd) = endpoints node

instance Matchable a b => Matchable (PrivTree1D a) (PrivTree1D b) where
  match (PrivTree1D a) (PrivTree1D b) =
    Prelude.and (MM.merge whenMissing whenMissing whenMatched a b)
    where whenMissing = MM.mapMissing (\_ _ -> False)
          whenMatched = MM.zipWithMatched (const match) -- \_ a b -> match a b

precedence :: M.Map Text Int
precedence = M.fromList [("||", 0), ("&&", 1),
                         ("==", 2),
                         ("<", 3), ("<=", 3), (">", 3), (">=", 3),
                         ("+", 4), ("-", 4),
                         ("*", 5), ("/", 5),
                         ("app", 1000000) -- function application
                        ]

fixity :: M.Map Text Int
fixity = M.fromList [("||", 0),
                     ("&&", 1),
                     ("==", 0),
                     ("<", 0), ("<=", 0),
                     (">", 0), (">=", 0),
                     ("+", 1), ("-", 1),
                     ("*", 1), ("/", 1),
                     ("app", 1) -- function application
                    ]

commaSep :: TPP.Doc -> TPP.Doc -> TPP.Doc
commaSep a b = a TPP.<> TPP.comma TPP.<+> b

reduceSubst :: SymbolicExpr -> SymbolicExpr
reduceSubst e = doSubst e []

reduceSubstB :: BoolExpr -> BoolExpr
reduceSubstB = coerce reduceSubst

doSubst :: SymbolicExpr -> [(String, SymbolicExpr)] -> SymbolicExpr
doSubst (RealVar x) substs =
  case find (\(f, _) -> f == x) substs of
    Nothing -> RealVar x
    Just (_, t) -> t
doSubst e@(Rat _) _ = e
doSubst e@(JustBool _) _ = e
doSubst (Add x y)      substs = Add (doSubst x substs) (doSubst y substs)
doSubst (Sub x y)      substs = Sub (doSubst x substs) (doSubst y substs)
doSubst (Mul x y)      substs = Mul (doSubst x substs) (doSubst y substs)
doSubst (Div x y)      substs = Div (doSubst x substs) (doSubst y substs)
doSubst (Lt x y)       substs = Lt  (doSubst x substs) (doSubst y substs)
doSubst (Le x y)       substs = Le  (doSubst x substs) (doSubst y substs)
doSubst (Gt x y)       substs = Gt  (doSubst x substs) (doSubst y substs)
doSubst (Ge x y)       substs = Ge  (doSubst x substs) (doSubst y substs)
doSubst (Eq_ x y)      substs = Eq_ (doSubst x substs) (doSubst y substs)
doSubst (And x y)      substs = And (doSubst x substs) (doSubst y substs)
doSubst (Or x y)       substs = Or  (doSubst x substs) (doSubst y substs)
doSubst (Not x)        substs = Not (doSubst x substs)
doSubst (Ite cond x y) substs = Ite (doSubst cond substs)
                                    (doSubst x substs)
                                    (doSubst y substs)
doSubst (Substitute x substs) substs' = doSubst x (substs ++ substs')

ite' :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr
ite' cond a b
  | a == b    = a
  | otherwise = Ite cond a b

tryEvalBool :: BoolExpr -> Maybe Bool
tryEvalBool = tryEvalBool' . getBoolExpr

tryEvalBool' :: SymbolicExpr -> Maybe Bool
tryEvalBool' (JustBool b) = Just b
tryEvalBool' (Lt a b)  = (<)  <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalBool' (Le a b)  = (<=) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalBool' (Gt a b)  = (>)  <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalBool' (Ge a b)  = (>=) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalBool' (Eq_ a b) =
  case (==) <$> tryEvalReal' a <*> tryEvalReal' b of
    Just a -> Just a
    Nothing -> (==) <$> tryEvalBool' a <*> tryEvalBool' b
tryEvalBool' (And a b) = (&&) <$> tryEvalBool' a <*> tryEvalBool' b
tryEvalBool' (Or  a b) = (||) <$> tryEvalBool' a <*> tryEvalBool' b
tryEvalBool' (Not a)   = not <$> tryEvalBool' a
tryEvalBool' (Ite cond a b) = do
  cond' <- tryEvalBool' cond
  if cond'
  then tryEvalBool' a
  else tryEvalBool' b
tryEvalBool' _ = Nothing

tryEvalReal :: RealExpr -> Maybe Rational
tryEvalReal = tryEvalReal' . getRealExpr

tryEvalInt :: IntExpr -> Maybe Integer
tryEvalInt = tryEvalInt' . getIntExpr

tryEvalReal' :: SymbolicExpr -> Maybe Rational
tryEvalReal' (Rat v) = Just v
tryEvalReal' (JustInt v) = Just $ fromInteger v
tryEvalReal' (Add a b) = (+) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalReal' (Sub a b) = (-) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalReal' (Mul a b) = (*) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalReal' (Div a b) = (/) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalReal' (Ite cond a b) = do
  cond' <- tryEvalBool' cond
  if cond'
  then tryEvalReal' a
  else tryEvalReal' b
tryEvalReal' _ = Nothing

tryEvalInt' :: SymbolicExpr -> Maybe Integer
tryEvalInt' (JustInt v) = Just v
tryEvalInt' (Add a b) = (+) <$> tryEvalInt' a <*> tryEvalInt' b
tryEvalInt' (Sub a b) = (-) <$> tryEvalInt' a <*> tryEvalInt' b
tryEvalInt' (Mul a b) = (*) <$> tryEvalInt' a <*> tryEvalInt' b
tryEvalInt' (Ite cond a b) = do
  cond' <- tryEvalBool' cond
  if cond'
  then tryEvalInt' a
  else tryEvalInt' b
tryEvalInt' _ = Nothing

sReal :: String -> RealExpr
sReal = RealExpr k_FLOAT_TOLERANCE . RealVar

sReal' :: Rational -> String -> RealExpr
sReal' tol = RealExpr tol . RealVar

k_FLOAT_TOLERANCE :: Rational
k_FLOAT_TOLERANCE = 1e-6

instance Applicative Guarded where
  pure = MkGuarded (bool True)
  (MkGuarded cond1 f) <*> (MkGuarded cond2 a) =
    MkGuarded (cond1 `and` cond2) (f a)

instance SEq Int Int where
  symEq a b = bool (a == b)

instance SEq Bool Bool where
  symEq a b = bool (a == b)

instance SEq Double RealExpr where
  symEq a b =
    let tol = getTolerance b
    in if tol == 0
    then double a %== b
    else abs (double a - b) %<= fromRational (getTolerance b)

instance SEq RealExpr RealExpr where
  symEq (getRealExpr -> a) (getRealExpr -> b) =
    BoolExpr (a `Eq_` b)

instance (SEq a b, SEq c d) => SEq (a, c) (b, d) where
  symEq (a, c) (b, d) =
    BoolExpr (And (getBoolExpr (a `symEq` b)) (getBoolExpr (c `symEq` d)))

instance SEq a b => SEq (Maybe a) (Maybe b) where
  symEq (Just a) (Just b) = symEq a b
  symEq Nothing  Nothing  = bool True
  symEq _        _        = bool False

instance SEq a b => SEq [a] [b] where
  symEq [] []         = BoolExpr (JustBool True)
  symEq (x:xs) (y:ys) =
    BoolExpr $
    And (getBoolExpr (x `symEq` y))
        (getBoolExpr (xs `symEq` ys))
  symEq _      _      = BoolExpr (JustBool False)

instance SEq a b => SEq (PrivTree1D a) (PrivTree1D b) where
  symEq (PrivTree1D a) (PrivTree1D b) =
    case MM.mergeA whenMissing whenMissing whenMatched a b of
      Nothing         -> bool False
      Just equalities -> foldr and (bool True) equalities
    where whenMissing = MM.traverseMissing (\_ _ -> Nothing)
          whenMatched = MM.zipWithAMatched (\_ c s -> Just (symEq c s))
