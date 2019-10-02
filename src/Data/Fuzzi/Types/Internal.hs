module Data.Fuzzi.Types.Internal where

import Control.Lens hiding (matching)
import Control.Monad.Catch
import Data.Bifunctor
import Data.Coerce
import Data.Functor.Compose
import Data.Fuzzi.IfCxt
import Data.Fuzzi.Types.SymbolicExpr
import Data.Fuzzi.Types.Optimize
import Data.List (find)
import Data.Maybe
import Data.Text (Text)
import Prelude hiding (and, or)
import Type.Reflection
import qualified Data.Map.Merge.Strict as MM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Prelude

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
class Ord a => SymbolicRepr a where
  reduceable :: a -> a -> Bool
  merge :: BoolExpr
        -> a
        -> a
        -> GuardedSymbolicUnion a

-- |This typeclass is defined for values that we can establish a symbolic
-- equality condition over.
class Matchable a b => SEq a b where
  symEq :: a -> b -> BoolExpr

infix 4 %<, %<=, %>, %>=, %==, %/=
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

infixr 3 `and`
infixr 2 `or`
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

instance Boolean BoolExpr where
  -- we only optimize `and` so that condensing symbolic unions do not cause
  -- boolean expression explosion
  and (tryEvalBool -> Just True) b  = b
  and a (tryEvalBool -> Just True)  = a
  and (tryEvalBool -> Just False) _ = bool False
  and _ (tryEvalBool -> Just False) = bool False
  and a b | a == b    = a
          | otherwise = optimizeBool $ coerce And a b
  or  (tryEvalBool -> Just False) b = b
  or  b (tryEvalBool -> Just False) = b
  or  (tryEvalBool -> Just True) _ = bool True
  or  _ (tryEvalBool -> Just True) = bool True
  or  a b | a == neg b = bool True
          | neg a == b = bool True
          | otherwise = optimizeBool $ coerce Or a b
  neg = coerce Not

instance Ordered RealExpr where
  type CmpResult RealExpr = BoolExpr

  lhs %< rhs  = BoolExpr (getRealExpr lhs `Lt` getRealExpr rhs)
  lhs %<= rhs = BoolExpr (getRealExpr lhs `Le` getRealExpr rhs)
  lhs %> rhs  = BoolExpr (getRealExpr lhs `Gt` getRealExpr rhs)
  lhs %>= rhs = BoolExpr (getRealExpr lhs `Ge` getRealExpr rhs)
  lhs %== rhs = BoolExpr (getRealExpr lhs `Eq_` getRealExpr rhs)
  a %/= b = neg (a %== b)

instance Ordered IntExpr where
  type CmpResult IntExpr = BoolExpr

  (%<)  = coerce Lt
  (%<=) = coerce Le
  (%>)  = coerce Gt
  (%>=) = coerce Ge
  (%==) = coerce Eq_
  a %/= b = neg (a %== b)

instance Numeric     IntExpr
instance Numeric     RealExpr
instance FracNumeric RealExpr
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
  match (tryEvalBool -> Just b1) (tryEvalBool -> Just b2) = b1 == b2
  match _                        _                        = True

instance Matchable IntExpr  IntExpr where
  match (tryEvalInt -> Just i1) (tryEvalInt -> Just i2) = i1 == i2
  match _                       _                       = True

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

reduceSubst :: SymbolicExpr -> SymbolicExpr
reduceSubst e = doSubst e []

reduceSubstB :: BoolExpr -> BoolExpr
reduceSubstB = coerce reduceSubst

doSubst :: SymbolicExpr -> [(String, SymbolicExpr)] -> SymbolicExpr
doSubst (RealVar x) substs =
  case find (\(f, _) -> f == x) substs of
    Nothing -> RealVar x
    Just (_, t) -> t
doSubst (RealArrayVar x) substs =
  case find (\(f, _) -> f == x) substs of
    Nothing -> RealArrayVar x
    Just (_, t) -> t
doSubst e@(Rat _) _ = e
doSubst e@(JustBool _) _ = e
doSubst e@(JustInt _) _ = e
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
doSubst (RealArrayIndex arr idx) substs = RealArrayIndex (doSubst arr substs) (doSubst idx substs)
doSubst (Substitute x substs) substs' = doSubst x (substs ++ substs')

ite' :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr
ite' cond a b
  | a == b    = a
  | otherwise = Ite cond a b

simplifyBool :: BoolExpr -> BoolExpr
simplifyBool b = maybe b bool (tryEvalBool b)

simplifyInt :: IntExpr -> IntExpr
simplifyInt b = maybe b int (tryEvalInt b)

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
tryEvalReal' (Div a b) =
  case tryEvalReal' b of
    Just 0 -> Nothing
    _ -> (/) <$> tryEvalReal' a <*> tryEvalReal' b
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

sArray :: String -> ArrayExpr
sArray = ArrayExpr . RealArrayVar

at' :: Rational -> ArrayExpr -> IntExpr -> RealExpr
at' tol (ArrayExpr arr) (IntExpr idx) = RealExpr tol (RealArrayIndex arr idx)

at :: ArrayExpr -> IntExpr -> RealExpr
at = at' k_FLOAT_TOLERANCE

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
