{-# LANGUAGE DerivingVia #-}
module EDSL where

import Data.Coerce
import Data.Functor.Compose
import Control.Monad.Codensity
import Type.Reflection (Typeable, typeRep, eqTypeRep, (:~~:)(..))

-- |This constraint is only satisfied by first-class datatypes supported in
-- Fuzzi.
class FuzziType (a :: *)

-- |Order operators in the semantic domain.
class (Boolean (CmpResult a), Typeable a) => Ordered (a :: *) where
  type CmpResult a :: *
  (%<)  :: a -> a -> CmpResult a
  (%<=) :: a -> a -> CmpResult a
  (%>)  :: a -> a -> CmpResult a
  (%>=) :: a -> a -> CmpResult a
  (%==) :: a -> a -> CmpResult a
  (%/=) :: a -> a -> CmpResult a

-- |This constraint is only satisfied by numeric datatypes supported in Fuzzi.
class (Ordered a, Num a, Typeable a) => Numeric (a :: *)
class (Numeric a, Fractional a) => FracNumeric (a :: *)

-- |Boolean operators in the semantic domain.
class (Typeable a) => Boolean (a :: *) where
  and :: a -> a -> a
  or  :: a -> a -> a
  neg :: a -> a

-- |Sample instructions in the semantic domain.
class (Monad m, Typeable m) => MonadDist m where
  laplace  :: (FracNumeric a) => a -> Double -> m a
  gaussian :: (FracNumeric a) => a -> Double -> m a

-- |The main typeclass for reification and reflection.
class Syntactic a where
  type DeepRepr a :: *
  toDeepRepr      :: a -> Fuzzi (DeepRepr a)
  fromDeepRepr    :: Fuzzi (DeepRepr a) -> a

data Mon m a = Mon { runMon :: forall b. (Typeable b) => (a -> Fuzzi (m b)) -> Fuzzi (m b) }
  deriving (Functor)--, Applicative, Monad)
  -- via (Codensity (Compose Fuzzi m))

instance Applicative (Mon m) where
  pure a  = Mon $ \k -> k a
  f <*> a = f >>= \f' -> a >>= \a' -> return (f' a')

instance Monad (Mon m) where
  return a = Mon $ \k -> k a
  Mon m >>= f = Mon $ \k -> m (\a -> runMon (f a) k)

data Fuzzi (a :: *) where
  Lam         :: (FuzziType a, Typeable a, Typeable b) => (Fuzzi a -> Fuzzi b) -> Fuzzi (a -> b)
  App         :: (Typeable a) => Fuzzi (a -> b) -> Fuzzi a -> Fuzzi b

  Return      :: (Monad m, Typeable a) => Fuzzi a -> Fuzzi (m a)
  Bind        :: (Monad m, Typeable m, Typeable a) => Fuzzi (m a) -> (Fuzzi (a -> m b)) -> Fuzzi (m b)
  Lit         :: FuzziType a    => a -> Fuzzi a
  If          :: (Boolean bool, Typeable a) => Fuzzi bool -> Fuzzi a -> Fuzzi a -> Fuzzi a
  Laplace     :: (Numeric a, MonadDist m) => Fuzzi a -> Double -> Fuzzi (m a)
  Gaussian    :: (Numeric a, MonadDist m) => Fuzzi a -> Double -> Fuzzi (m a)
  Variable    :: (Typeable a) => Int -> Fuzzi a

  And         :: (Boolean bool) => Fuzzi bool -> Fuzzi bool -> Fuzzi bool
  Or          :: (Boolean bool) => Fuzzi bool -> Fuzzi bool -> Fuzzi bool
  Not         :: (Boolean bool) => Fuzzi bool -> Fuzzi bool

  Add         :: (Numeric a) => Fuzzi a -> Fuzzi a -> Fuzzi a
  Mult        :: (Numeric a) => Fuzzi a -> Fuzzi a -> Fuzzi a
  Sub         :: (Numeric a) => Fuzzi a -> Fuzzi a -> Fuzzi a
  Sign        :: (Numeric a) => Fuzzi a -> Fuzzi a
  Abs         :: (Numeric a) => Fuzzi a -> Fuzzi a

  Div         :: (Numeric a) => Fuzzi a -> Fuzzi a -> Fuzzi a

  Lt          :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)
  Le          :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)
  Gt          :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)
  Ge          :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)
  Eq_         :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)
  Neq         :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)

  AssertTrue  :: (Boolean bool) => Fuzzi bool -> Fuzzi a -> Fuzzi a
  AssertFalse :: (Boolean bool) => Fuzzi bool -> Fuzzi a -> Fuzzi a

if_ :: (Syntactic a, Boolean bool, Typeable bool, Typeable (DeepRepr a)) => Fuzzi bool -> a -> a -> a
if_ c t f = fromDeepRepr $ If c (toDeepRepr t) (toDeepRepr f)

lap :: (Numeric a, MonadDist m, FuzziType a) => Fuzzi a -> Double -> Mon m (Fuzzi a)
lap c w = fromDeepRepr $ Laplace c w -- Mon ((Bind (Laplace c w)))

gauss :: (Numeric a, MonadDist m, FuzziType a) => Fuzzi a -> Double -> Mon m (Fuzzi a)
gauss c w = fromDeepRepr $ Gaussian c w --  Mon ((Bind (Gaussian c w)))

reify :: (Syntactic a) => a -> Fuzzi (DeepRepr a)
reify a = toDeepRepr a

subst :: forall varType a. (Typeable varType, Typeable a) => Int -> Fuzzi a -> Fuzzi varType -> Fuzzi a
subst v term filling =
  case term of
    Lam f -> Lam $ \x -> subst v (f $ Variable v) filling
    App f a -> App (subst v f filling) (subst v a filling)

    Return x -> Return $ subst v x filling
    Bind a f -> Bind (subst v a filling) (subst v f filling)

    Lit x -> Lit x
    If cond t f -> If (subst v cond filling) (subst v t filling) (subst v f filling)
    Laplace c w -> Laplace (subst v c filling) w
    Gaussian c w -> Gaussian (subst v c filling) w

    Variable v' ->
      case (v == v', eqTypeRep (typeRep @varType) (typeRep @a)) of
        (True, Just HRefl) -> filling
        _                  -> Variable v'

    And a b -> And (subst v a filling) (subst v b filling)
    Or  a b -> Or  (subst v a filling) (subst v b filling)
    Not a   -> Not (subst v a filling)

    Add  a b -> Add  (subst v a filling) (subst v b filling)
    Mult a b -> Mult (subst v a filling) (subst v b filling)
    Sub  a b -> Sub  (subst v a filling) (subst v b filling)
    Sign a   -> Sign (subst v a filling)
    Abs  a   -> Abs  (subst v a filling)

    Div  a b -> Div  (subst v a filling) (subst v b filling)

    Lt  a b  -> Lt   (subst v a filling) (subst v b filling)
    Le  a b  -> Le   (subst v a filling) (subst v b filling)
    Gt  a b  -> Gt   (subst v a filling) (subst v b filling)
    Ge  a b  -> Ge   (subst v a filling) (subst v b filling)
    Eq_  a b -> Eq_  (subst v a filling) (subst v b filling)
    Neq  a b -> Neq  (subst v a filling) (subst v b filling)

    AssertTrue cond a  -> AssertTrue (subst v cond filling) (subst v a filling)
    AssertFalse cond a -> AssertFalse (subst v cond filling) (subst v a filling)

streamline :: Typeable a => Fuzzi a -> [Fuzzi a]
streamline = streamlineAux 0

streamlineAux :: Typeable a => Int -> Fuzzi a -> [Fuzzi a]
streamlineAux var (Lam (f :: Fuzzi x -> Fuzzi y)) =
  let bodies = streamlineAux (var + 1) (f (Variable var))
  in [Lam (\x -> subst @x var body x) | body <- bodies]
streamlineAux var (App f a) =
  [App f' a' | f' <- streamlineAux var f, a' <- streamlineAux var a]
streamlineAux var (Return x) =
  [Return x' | x' <- streamlineAux var x]
streamlineAux var (Bind a f) =
  [Bind a' f' | a' <- streamlineAux var a, f' <- streamlineAux var f]
streamlineAux _ (Lit x) = [Lit x]
streamlineAux var (If cond t f) =
  let conds = streamlineAux var cond
  in [AssertTrue cond' t' | cond' <- conds, t' <- streamlineAux var t]
     ++ [AssertFalse cond' f' | cond' <- conds, f' <- streamlineAux var f]
streamlineAux var (Laplace c w) =
  [Laplace c' w | c' <- streamlineAux var c]
streamlineAux var (Gaussian c w) =
  [Gaussian c' w | c' <- streamlineAux var c]
streamlineAux _ v@(Variable _) = [v]
streamlineAux var (And a b) =
  [And a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Or  a b) =
  [Or a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Not a) =
  [Not a' | a' <- streamlineAux var a]
streamlineAux var (Add a b) =
  [Add a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Mult a b) =
  [Mult a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Sub a b) =
  [Sub a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Sign a) =
  [Sign a' | a' <- streamlineAux var a]
streamlineAux var (Abs a) =
  [Abs a' | a' <- streamlineAux var a]
streamlineAux var (Div a b) =
  [Div a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Lt a b) =
  [Lt a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Le a b) =
  [Le a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Gt a b) =
  [Gt a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Ge a b) =
  [Ge a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Eq_ a b) =
  [Eq_ a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Neq a b) =
  [Neq a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (AssertTrue cond a) =
  [AssertTrue cond' a' | cond' <- streamlineAux var cond, a' <- streamlineAux var a]
streamlineAux var (AssertFalse cond a) =
  [AssertFalse cond' a' | cond' <- streamlineAux var cond, a' <- streamlineAux var a]

instance ( Syntactic a
         , Syntactic b
         , Typeable (DeepRepr a)
         , Typeable (DeepRepr b)
         , FuzziType (DeepRepr a)) => Syntactic (a -> b) where
  type DeepRepr (a -> b) = (DeepRepr a -> DeepRepr b)
  toDeepRepr f = Lam (toDeepRepr . f . fromDeepRepr)
  fromDeepRepr f = fromDeepRepr . (App f) . toDeepRepr

instance Syntactic (Fuzzi a) where
  type DeepRepr (Fuzzi a) = a
  toDeepRepr   = id
  fromDeepRepr = id

instance ( Monad m
         , Syntactic a
         , FuzziType (DeepRepr a)
         , Typeable (DeepRepr a)
         , Typeable m) => Syntactic (Mon m a) where
  type DeepRepr (Mon m a) = m (DeepRepr a)
  toDeepRepr (Mon m) = m (Return . toDeepRepr)
  fromDeepRepr    m  = Mon $ \k -> Bind m (toDeepRepr $ k . fromDeepRepr)

instance Boolean Bool where
  and = (&&)
  or  = (||)
  neg = not

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
  (%<)  = (<)
  (%<=) = (<=)
  (%>)  = (>)
  (%>=) = (>=)
  (%==) = (==)
  (%/=) = (/=)

instance FuzziType Double
instance FuzziType Bool
instance FuzziType Int

instance Numeric Double
instance FracNumeric Double
instance Numeric Int

instance (FuzziType a, Numeric a) => Num (Fuzzi a) where
  (+) = coerce Add
  (-) = coerce Sub
  (*) = coerce Mult
  abs = coerce Abs
  signum = coerce Sign
  fromInteger = Lit . fromInteger

instance (FuzziType a, FracNumeric a) => Fractional (Fuzzi a) where
  (/)          = coerce Div
  fromRational = Lit . fromRational

instance ( Boolean (CmpResult a)
         , Boolean (Fuzzi (CmpResult a))
         , Ordered a) => Ordered (Fuzzi a) where
  type CmpResult (Fuzzi a) = Fuzzi (CmpResult a)
  (%<)  = Lt
  (%<=) = Le
  (%>)  = Gt
  (%>=) = Ge
  (%==) = Eq_
  (%/=) = Neq

instance Boolean a => Boolean (Fuzzi a) where
  and = And
  or  = Or
  neg = Not

ex1 :: (MonadDist m, Typeable m) => Mon m (Fuzzi Double)
ex1 = do
  x1 <- lap (Lit (1.0 :: Double)) 1.0
  x2 <- lap (Lit 2.0) 1.0
  return $ x1 + x2

ex2 :: (MonadDist m, Typeable m) => Mon m (Fuzzi Double)
ex2 = do
  x1 <- lap 1.0 1.0
  x2 <- lap x1 1.0
  return $ x1 + x2

ex3 :: Fuzzi Double -> Fuzzi Double -> Fuzzi Double
ex3 a b = if_ (a %> b) a b

ex4 :: (MonadDist m) => Mon m (Fuzzi Double)
ex4 = do
  x1 <- lap 1.0 1.0
  x2 <- lap 1.0 1.0
  if_ (x1 %> x2)
      (do x3 <- gauss 1.0 1.0
          return $ if_ (x3 %> x1) x3 x1
      )
      (do x4 <- gauss 1.0 1.0
          return $ if_ (x4 %> x2) x4 x2
      )

reportNoisyMaxAux :: ( MonadDist   m
                     , FracNumeric a
                     , FuzziType   a)
                  => [Fuzzi a]
                  -> Fuzzi Int
                  -> Fuzzi Int
                  -> Fuzzi a
                  -> Mon m (Fuzzi Int)
reportNoisyMaxAux []     _       maxIdx _       = return maxIdx
reportNoisyMaxAux (x:xs) currIdx maxIdx currMax = do
  xNoised <- lap x 1.0
  if_ (xNoised %> currMax)
      (reportNoisyMaxAux xs (currIdx + 1) currIdx xNoised)
      (reportNoisyMaxAux xs (currIdx + 1) maxIdx  currMax)

reportNoisyMax :: ( MonadDist   m
                  , FracNumeric a
                  , FuzziType   a)
               => [Fuzzi a]
               -> Mon m (Fuzzi Int)
reportNoisyMax []     = error "reportNoisyMax received empty input"
reportNoisyMax (x:xs) = do
  xNoised <- lap x 1.0
  reportNoisyMaxAux xs 0 0 xNoised

instance MonadDist IO
