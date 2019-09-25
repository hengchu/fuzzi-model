module Data.Fuzzi.Types where

import Control.Monad.Catch
import Data.Bifunctor
import Data.Coerce
import Data.Functor.Compose
import Data.Fuzzi.IfCxt
import Data.Kind (Constraint)
import Data.Text (Text)
import GHC.TypeLits
import Prelude hiding (and)
import Type.Reflection
import qualified Data.Map.Merge.Strict as MM
import qualified Data.Map.Strict as M
import qualified Prelude
import qualified Text.PrettyPrint as TPP

singleton :: a -> SymbolicUnion a
singleton = Singleton

guarded :: a -> Guarded a
guarded = MkGuarded (bool True)

type GuardedSymbolicUnion = Compose SymbolicUnion Guarded

class SymbolicRepr a where
  into  :: a
        -> GuardedSymbolicUnion a
  merge :: Guarded a
        -> GuardedSymbolicUnion a
        -> GuardedSymbolicUnion a

newtype IntExpr = IntExpr { getIntExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord)

data Guarded (a :: *) where
  MkGuarded :: BoolExpr -> a -> Guarded a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data SymbolicUnion (a :: *) where
  Singleton :: a -> SymbolicUnion a
  Union     :: SymbolicUnion a -> SymbolicUnion a -> SymbolicUnion a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- |This constraint is only satisfied by first-class datatypes supported in
-- Fuzzi.
class (Typeable a, Show a) => FuzziType (a :: *)

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

class (Monad m, Typeable m, Boolean (BoolType m), MonadThrow m) => MonadAssert m where
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
  show = pretty

pretty :: SymbolicExpr -> String
pretty = TPP.render . prettySymbolic 0

parensIf :: Bool -> TPP.Doc -> TPP.Doc
parensIf True  = TPP.parens
parensIf False = id

prettySymbolic :: Int -> SymbolicExpr -> TPP.Doc
prettySymbolic _ (RealVar x) = TPP.text x
prettySymbolic _ (Rat r) = TPP.text (show r) --TPP.double (fromRational r)
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

double :: Double -> RealExpr
double = fromRational . toRational

bool :: Bool -> BoolExpr
bool = BoolExpr . JustBool

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

instance Fractional RealExpr where
  RealExpr tol left / RealExpr tol' right = RealExpr (max tol tol') (Div left right)
  fromRational = RealExpr 0 . Rat

instance Boolean BoolExpr where
  and = coerce And
  or  = coerce Or
  neg = coerce Not

instance Ordered RealExpr where
  type CmpResult RealExpr = BoolExpr

  lhs %< rhs  = BoolExpr (getRealExpr lhs `Lt` getRealExpr rhs)
  lhs %<= rhs = BoolExpr (getRealExpr lhs `Le` getRealExpr rhs)
  lhs %> rhs  = BoolExpr (getRealExpr lhs `Gt` getRealExpr rhs)
  lhs %>= rhs = BoolExpr (getRealExpr lhs `Ge` getRealExpr rhs)
  lhs %== rhs = BoolExpr (getRealExpr lhs `Eq_` getRealExpr rhs)
  a %/= b = neg (a %== b)

instance SymbolicRepr Double where
  into = undefined
  merge = undefined

instance SymbolicRepr Bool where
  into = undefined
  merge = undefined

instance SymbolicRepr RealExpr where
  into = pure
  merge = undefined

instance SymbolicRepr BoolExpr where
  into = pure
  merge = undefined

instance Numeric     RealExpr
instance FracNumeric RealExpr
instance FuzziType   RealExpr
instance FuzziType   BoolExpr

instance FuzziType Double
instance FuzziType Bool
instance FuzziType Int
instance FuzziType a => FuzziType (PrivTree1D a)
instance FuzziType a => FuzziType [a]
instance FuzziType a => FuzziType (Maybe a)
instance FuzziType PrivTreeNode1D
instance (FuzziType a, FuzziType b) => FuzziType (a, b)

instance SymbolicRepr a => SymbolicRepr (PrivTree1D a) where
  into = undefined
  merge = undefined

instance SymbolicRepr a => SymbolicRepr [a] where
  into = undefined
  merge = undefined

instance SymbolicRepr a => SymbolicRepr (Maybe a) where
  into = undefined
  merge = undefined

instance (SymbolicRepr a, SymbolicRepr b) => SymbolicRepr (a, b) where
  into = undefined
  merge = undefined

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

instance Applicative Guarded where
  pure = guarded
  (MkGuarded cond1 f) <*> (MkGuarded cond2 a) =
    MkGuarded (cond1 `and` cond2) (f a)

instance Applicative SymbolicUnion where
  pure = Singleton
  (Singleton f)   <*> (Singleton a)   = Singleton (f a)
  (Singleton f)   <*> (u1 `Union` u2) = (fmap f u1) `Union` (fmap f u2)
  (f1 `Union` f2) <*> (Singleton a)   = (fmap ($ a) f1) `Union` (fmap ($ a) f2)
  (f1 `Union` f2) <*> (u1 `Union` u2) =
    (f1 <*> u1) `Union` (f1 <*> u2) `Union` (f2 <*> u1) `Union` (f2 <*> u2)
