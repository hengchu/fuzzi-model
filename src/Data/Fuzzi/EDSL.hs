{-# LANGUAGE DerivingVia #-}
module Data.Fuzzi.EDSL (
  Fuzzi(..)
  , Syntactic
  , Syntactic1
  , Mon

  , if_
  , ifM
  , lap
  , gauss
  , lap'
  , gauss'
  , fst_
  , snd_
  , pair
  , lit
  , true
  , false
  , abort
  , updatePT
  , nil
  , cons
  , snoc
  , just
  , nothing
  , isNil
  , length_
  , fromIntegral_
  , reify
  , streamline
  ) where

import Data.Coerce
import Type.Reflection (Typeable, typeRep, eqTypeRep, (:~~:)(..))
import Data.Fuzzi.Types hiding (SymbolicExpr(..))
import Control.Monad.Catch

newtype Mon m a = Mon { runMon :: forall b. (Typeable b) => (a -> Fuzzi (m b)) -> Fuzzi (m b) }
  deriving (Functor)--, Applicative, Monad)
  -- via (Codensity (Compose Fuzzi m))

-- |The main typeclass for reification and reflection.
class Typeable (DeepRepr a) => Syntactic a where
  type DeepRepr a :: *
  toDeepRepr      :: a -> Fuzzi (DeepRepr a)
  fromDeepRepr    :: Fuzzi (DeepRepr a) -> a

class Syntactic1 (m :: * -> *) where
  type DeepRepr1 m :: * -> *
  toDeepRepr1   :: (Syntactic a, FuzziType (DeepRepr a)) => m a -> Fuzzi (DeepRepr1 m (DeepRepr a))
  fromDeepRepr1 :: (Syntactic a, FuzziType (DeepRepr a)) => Fuzzi (DeepRepr1 m (DeepRepr a)) -> m a

data Fuzzi (a :: *) where
  Lam         :: (FuzziType a, FuzziType b) => (Fuzzi a -> Fuzzi b) -> Fuzzi (a -> b)
  App         :: (Typeable a) => Fuzzi (a -> b) -> Fuzzi a -> Fuzzi b

  Return      :: (Monad m, FuzziType a) => Fuzzi a -> Fuzzi (m a)
  Sequence    :: (Monad m, Typeable m, FuzziType a) => Fuzzi (m ()) -> Fuzzi (m a) -> Fuzzi (m a)
  Bind        :: (Monad m, Typeable m, FuzziType a, Typeable b) => Fuzzi (m a) -> (Fuzzi a -> Fuzzi (m b)) -> Fuzzi (m b)
  Lit         :: (FuzziType a) => a -> Fuzzi a
  If          :: (ConcreteBoolean bool) => Fuzzi bool -> Fuzzi a -> Fuzzi a -> Fuzzi a
  IfM         :: (FuzziType a, Assertion m bool) => Fuzzi bool -> Fuzzi (m a) -> Fuzzi (m a) -> Fuzzi (m a)
  Laplace     :: (Distribution m a) =>             Fuzzi a -> Double -> Fuzzi (m a)
  Laplace'    :: (Distribution m a) => Rational -> Fuzzi a -> Double -> Fuzzi (m a)
  Gaussian    :: (Distribution m a) =>             Fuzzi a -> Double -> Fuzzi (m a)
  Gaussian'   :: (Distribution m a) => Rational -> Fuzzi a -> Double -> Fuzzi (m a)
  Variable    :: (Typeable a) => Int -> Fuzzi a

  PrettyPrintVariable :: (Typeable a) => String -> Fuzzi a

  And         :: (Boolean bool) => Fuzzi bool -> Fuzzi bool -> Fuzzi bool
  Or          :: (Boolean bool) => Fuzzi bool -> Fuzzi bool -> Fuzzi bool
  Not         :: (Boolean bool) => Fuzzi bool -> Fuzzi bool

  Add         :: (Numeric a) => Fuzzi a -> Fuzzi a -> Fuzzi a
  Mult        :: (Numeric a) => Fuzzi a -> Fuzzi a -> Fuzzi a
  Sub         :: (Numeric a) => Fuzzi a -> Fuzzi a -> Fuzzi a
  Sign        :: (Numeric a) => Fuzzi a -> Fuzzi a
  Abs         :: (Numeric a) => Fuzzi a -> Fuzzi a

  Div         :: (FracNumeric a) => Fuzzi a -> Fuzzi a -> Fuzzi a
  IDiv        :: (IntNumeric a)  => Fuzzi a -> Fuzzi a -> Fuzzi a
  IMod        :: (IntNumeric a)  => Fuzzi a -> Fuzzi a -> Fuzzi a

  Lt          :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)
  Le          :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)
  Gt          :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)
  Ge          :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)
  Eq_         :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)
  Neq         :: (Ordered a) => Fuzzi a -> Fuzzi a -> Fuzzi (CmpResult a)

  AssertTrueM  :: (Assertion m bool) => Fuzzi bool -> Fuzzi (m ())
  AssertFalseM :: (Assertion m bool) => Fuzzi bool -> Fuzzi (m ())

  ListNil    :: (FuzziType a) => Fuzzi [a]
  ListCons   :: (FuzziType a) => Fuzzi a   -> Fuzzi [a] -> Fuzzi [a]
  ListSnoc   :: (FuzziType a) => Fuzzi [a] -> Fuzzi a   -> Fuzzi [a]
  ListIsNil  :: (FuzziType a, ConcreteBoolean bool) => Fuzzi [a] -> Fuzzi bool
  ListLength :: (FuzziType a) => Fuzzi [a] -> Fuzzi Int

  Just_      :: (FuzziType a) => Fuzzi a -> Fuzzi (Maybe a)
  Nothing_   :: (FuzziType a) => Fuzzi (Maybe a)

  Pair      :: (FuzziType a, FuzziType b) => Fuzzi a -> Fuzzi b      -> Fuzzi (a, b)
  Fst       :: (FuzziType a, FuzziType b) =>            Fuzzi (a, b) -> Fuzzi a
  Snd       :: (FuzziType a, FuzziType b) =>            Fuzzi (a, b) -> Fuzzi b

  NumCast   :: (FuzziType a, FuzziType b, Integral a, Num b) => Fuzzi a -> Fuzzi b

  Abort     :: (FuzziType a, Typeable m, MonadThrow m) => String -> Fuzzi (m a)

  UpdatePrivTree :: (FuzziType a) => Fuzzi PrivTreeNode1D -> Fuzzi a -> Fuzzi (PrivTree1D a) -> Fuzzi (PrivTree1D a)

just :: (FuzziType a) => Fuzzi a -> Fuzzi (Maybe a)
just = Just_

nothing :: (FuzziType a) => Fuzzi (Maybe a)
nothing = Nothing_

nil :: (FuzziType a) => Fuzzi [a]
nil = ListNil

cons :: (FuzziType a) => Fuzzi a -> Fuzzi [a] -> Fuzzi [a]
cons = ListCons

snoc :: (FuzziType a) => Fuzzi [a] -> Fuzzi a -> Fuzzi [a]
snoc = ListSnoc

isNil :: (FuzziType a, ConcreteBoolean bool) => Fuzzi [a] -> Fuzzi bool
isNil = ListIsNil

length_ :: (FuzziType a) => Fuzzi [a] -> Fuzzi Int
length_ = ListLength

updatePT :: (FuzziType a)
         => Fuzzi PrivTreeNode1D
         -> Fuzzi a
         -> Fuzzi (PrivTree1D a)
         -> Fuzzi (PrivTree1D a)
updatePT = UpdatePrivTree

abort :: ( FuzziType a
         , Typeable m
         , MonadThrow m
         ) => String -> Mon m (Fuzzi a)
abort reason = fromDeepRepr $ Abort reason

true :: Fuzzi Bool
true = Lit True

false :: Fuzzi Bool
false = Lit False

fromIntegral_ :: (FuzziType a, FuzziType b, Integral a, Num b) => Fuzzi a -> Fuzzi b
fromIntegral_ = NumCast

if_ :: (Syntactic a, ConcreteBoolean bool) => Fuzzi bool -> a -> a -> a
if_ c t f = fromDeepRepr $ If c (toDeepRepr t) (toDeepRepr f)

ifM :: ( Syntactic1 m
       , Syntactic a
       , Assertion (DeepRepr1 m) bool
       , FuzziType (DeepRepr a)) => Fuzzi bool -> m a -> m a -> m a
ifM c t f = fromDeepRepr1 $ IfM c (toDeepRepr1 t) (toDeepRepr1 f)

lap :: forall m a. Distribution m a => Fuzzi a -> Double -> Mon m (Fuzzi a)
lap c w = fromDeepRepr $ Laplace c w -- Mon ((Bind (Laplace c w)))

gauss :: forall m a. Distribution m a => Fuzzi a -> Double -> Mon m (Fuzzi a)
gauss c w = fromDeepRepr $ Gaussian c w --  Mon ((Bind (Gaussian c w)))

lap' :: forall m a. Distribution m a => Rational -> Fuzzi a -> Double -> Mon m (Fuzzi a)
lap' tol c w = fromDeepRepr $ Laplace' tol c w -- Mon ((Bind (Laplace c w)))

gauss' :: forall m a. Distribution m a => Rational -> Fuzzi a -> Double -> Mon m (Fuzzi a)
gauss' tol c w = fromDeepRepr $ Gaussian' tol c w --  Mon ((Bind (Gaussian c w)))

pair :: (FuzziType (DeepRepr a), FuzziType (DeepRepr b), Syntactic a, Syntactic b) => a -> b -> (a, b)
pair a b = fromDeepRepr $ Pair (toDeepRepr a) (toDeepRepr b)

fst_ :: (FuzziType a, FuzziType b) => Fuzzi (a, b) -> Fuzzi a
fst_ = Fst

snd_ :: (FuzziType a, FuzziType b) => Fuzzi (a, b) -> Fuzzi b
snd_ = Snd

lit :: (FuzziType a) => a -> Fuzzi a
lit = Lit

reify :: (Syntactic a) => a -> Fuzzi (DeepRepr a)
reify = optimize . toDeepRepr

extensionallyEqualToReturn :: forall a b m. (Typeable a, Typeable b)
                           => (Fuzzi a -> Fuzzi (m b)) -> Maybe (a :~~:b)
extensionallyEqualToReturn f =
  case eqTypeRep (typeRep @a) (typeRep @b) of
    Just HRefl -> case f (Variable 0) of
                    Return (Variable 0) -> Just HRefl
                    _                   -> Nothing
    _ -> Nothing

optimize :: Fuzzi a -> Fuzzi a
optimize e@(Bind _ _)     = simplBindReturn e
optimize e@(Sequence _ _) = simplBindReturn e
optimize (IfM cond a b)   = IfM cond (optimize a) (optimize b)
optimize e                = e

simplBindReturn :: forall b m. (Typeable b, Typeable m, Monad m) => Fuzzi (m b) -> Fuzzi (m b)
simplBindReturn (Bind a (f :: Fuzzi a -> Fuzzi (m b))) =
  case extensionallyEqualToReturn f of
    Just HRefl -> simplBindReturn a
    Nothing    -> Bind (simplBindReturn a) (simplBindReturn . f)
simplBindReturn (IfM cond a b) =
  IfM cond (simplBindReturn a) (simplBindReturn b)
simplBindReturn (Sequence a b) =
  Sequence (simplBindReturn a) (simplBindReturn b)
simplBindReturn e = e

subst :: forall varType a. (Typeable varType, Typeable a) => Int -> Fuzzi a -> Fuzzi varType -> Fuzzi a
subst v term filling =
  case term of
    Lam f -> Lam $ \x -> subst v (f x) filling
    App f a -> App (subst v f filling) (subst v a filling)

    Return x -> Return $ subst v x filling
    Sequence a b -> Sequence (subst v a filling) (subst v b filling)
    Bind a f -> Bind (subst v a filling) (\x -> subst v (f x) filling)

    Lit x -> Lit x
    If cond t f -> If (subst v cond filling) (subst v t filling) (subst v f filling)
    IfM cond t f -> IfM (subst v cond filling) (subst v t filling) (subst v f filling)
    Laplace c w -> Laplace (subst v c filling) w
    Gaussian c w -> Gaussian (subst v c filling) w
    Laplace' tol c w -> Laplace' tol (subst v c filling) w
    Gaussian' tol c w -> Gaussian' tol (subst v c filling) w

    Variable v' ->
      case (v == v', eqTypeRep (typeRep @varType) (typeRep @a)) of
        (True, Just HRefl) -> filling
        _                  -> Variable v'

    PrettyPrintVariable v' ->
      PrettyPrintVariable v'

    And a b -> And (subst v a filling) (subst v b filling)
    Or  a b -> Or  (subst v a filling) (subst v b filling)
    Not a   -> Not (subst v a filling)

    Add  a b -> Add  (subst v a filling) (subst v b filling)
    Mult a b -> Mult (subst v a filling) (subst v b filling)
    Sub  a b -> Sub  (subst v a filling) (subst v b filling)
    Sign a   -> Sign (subst v a filling)
    Abs  a   -> Abs  (subst v a filling)

    Div   a b -> Div   (subst v a filling) (subst v b filling)
    IDiv  a b -> IDiv  (subst v a filling) (subst v b filling)
    IMod  a b -> IMod  (subst v a filling) (subst v b filling)

    Lt  a b  -> Lt   (subst v a filling) (subst v b filling)
    Le  a b  -> Le   (subst v a filling) (subst v b filling)
    Gt  a b  -> Gt   (subst v a filling) (subst v b filling)
    Ge  a b  -> Ge   (subst v a filling) (subst v b filling)
    Eq_  a b -> Eq_  (subst v a filling) (subst v b filling)
    Neq  a b -> Neq  (subst v a filling) (subst v b filling)

    AssertTrueM cond -> AssertTrueM (subst v cond filling)
    AssertFalseM cond -> AssertFalseM (subst v cond filling)

    ListNil -> ListNil
    ListCons x xs -> ListCons (subst v x filling)  (subst v xs filling)
    ListSnoc xs x -> ListSnoc (subst v xs filling) (subst v x filling)
    ListIsNil xs  -> ListIsNil (subst v xs filling)
    ListLength xs -> ListLength (subst v xs filling)
    -- ListFilter f xs -> ListFilter (subst v f filling) (subst v xs filling)

    Just_ x -> Just_ (subst v x filling)
    Nothing_ -> Nothing_

    NumCast a -> NumCast (subst v a filling)

    Pair a b -> Pair (subst v a filling) (subst v b filling)
    Fst p -> Fst (subst v p filling)
    Snd p -> Snd (subst v p filling)

    Abort reason -> Abort reason

    UpdatePrivTree node value tree ->
      UpdatePrivTree (subst v node filling) (subst v value filling) (subst v tree filling)

streamline :: Typeable a => Fuzzi a -> [Fuzzi a]
streamline = map optimize . streamlineAux 0

streamlineAux :: Typeable a => Int -> Fuzzi a -> [Fuzzi a]
streamlineAux var (Lam (f :: Fuzzi x -> Fuzzi y)) =
  let bodies = streamlineAux (var + 1) (f (Variable var))
  in [Lam (subst @x var body) | body <- bodies]
streamlineAux var (App f a) =
  [App f' a' | f' <- streamlineAux var f, a' <- streamlineAux var a]
streamlineAux var (Return x) =
  [Return x' | x' <- streamlineAux var x]
streamlineAux var (Sequence a b) =
  [Sequence a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Bind a (f :: Fuzzi a -> Fuzzi (m b))) =
  let bodies = streamlineAux (var + 1) (f (Variable var))
  in [Bind a' (subst @a var body') | a' <- streamlineAux var a, body' <- bodies]
streamlineAux _ (Lit x) = [Lit x]
streamlineAux var (If cond t f) =
  [If cond' t' f' | cond' <- streamlineAux var cond, t' <- streamlineAux var t, f' <- streamlineAux var f]
streamlineAux var (IfM cond t f) =
  let conds = streamlineAux var cond
  in [Sequence (AssertTrueM cond') t' | cond' <- conds, t' <- streamlineAux var t]
     ++ [Sequence (AssertFalseM cond') f' | cond' <- conds, f' <- streamlineAux var f]
streamlineAux var (Laplace c w) =
  [Laplace c' w | c' <- streamlineAux var c]
streamlineAux var (Gaussian c w) =
  [Gaussian c' w | c' <- streamlineAux var c]
streamlineAux var (Laplace' tol c w) =
  [Laplace' tol c' w | c' <- streamlineAux var c]
streamlineAux var (Gaussian' tol c w) =
  [Gaussian' tol c' w | c' <- streamlineAux var c]
streamlineAux _ v@(Variable _) = [v]
streamlineAux _ v@(PrettyPrintVariable _) = [v]
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
streamlineAux var (IDiv a b) =
  [IDiv a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (IMod a b) =
  [IMod a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
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
streamlineAux var (AssertTrueM cond) =
  [AssertTrueM cond' | cond' <- streamlineAux var cond]
streamlineAux var (AssertFalseM cond) =
  [AssertFalseM cond' | cond' <- streamlineAux var cond]
streamlineAux _ ListNil = [ListNil]
streamlineAux var (ListCons x xs) =
  [ListCons x' xs' | x' <- streamlineAux var x, xs' <- streamlineAux var xs]
streamlineAux var (ListSnoc xs x) =
  [ListSnoc xs' x' | xs' <- streamlineAux var xs, x' <- streamlineAux var x]
streamlineAux var (ListIsNil x) =
  [ListIsNil x' | x' <- streamlineAux var x]
streamlineAux var (ListLength x) =
  [ListLength x' | x' <- streamlineAux var x]
--streamlineAux var (ListFilter f xs) =
--  [ListFilter f' xs' | f' <- streamlineAux var f, xs' <- streamlineAux var xs]
streamlineAux var (Pair a b) =
  [Pair a' b' | a' <- streamlineAux var a, b' <- streamlineAux var b]
streamlineAux var (Fst p) =
  Fst <$> streamlineAux var p
streamlineAux var (Snd p) =
  Snd <$> streamlineAux var p
streamlineAux var (NumCast x) =
  NumCast <$> streamlineAux var x
streamlineAux _var (Abort reason) =
  [Abort reason]
streamlineAux var (UpdatePrivTree node value tree) =
  [UpdatePrivTree node' value' tree' | node' <- streamlineAux var node, value' <- streamlineAux var value, tree' <- streamlineAux var tree]
streamlineAux var (Just_ x) =
  Just_ <$> streamlineAux var x
streamlineAux _ Nothing_ =
  [Nothing_]

instance Applicative (Mon m) where
  pure a  = Mon $ \k -> k a
  f <*> a = f >>= \f' -> a >>= \a' -> return (f' a')

instance Monad (Mon m) where
  return a = Mon $ \k -> k a
  Mon m >>= f = Mon $ \k -> m (\a -> runMon (f a) k)

instance ( Syntactic a
         , Syntactic b
         , FuzziType (DeepRepr a)
         , FuzziType (DeepRepr b)) => Syntactic (a, b) where
  type DeepRepr (a, b) = (DeepRepr a, DeepRepr b)
  toDeepRepr   (a, b)  = Pair (toDeepRepr a) (toDeepRepr b)
  fromDeepRepr pair    = (fromDeepRepr (Fst pair), fromDeepRepr (Snd pair))

instance ( Syntactic a
         , Syntactic b
         , FuzziType (DeepRepr a)
         , FuzziType (DeepRepr b)) => Syntactic (a -> b) where
  type DeepRepr (a -> b) = (DeepRepr a -> DeepRepr b)
  toDeepRepr f = Lam (toDeepRepr . f . fromDeepRepr)
  fromDeepRepr f = fromDeepRepr . App f . toDeepRepr

instance Typeable a => Syntactic (Fuzzi a) where
  type DeepRepr (Fuzzi a) = a
  toDeepRepr   = id
  fromDeepRepr = id

instance ( Monad m
         , Syntactic a
         , FuzziType (DeepRepr a)
         , Typeable m) => Syntactic (Mon m a) where
  type DeepRepr (Mon m a) = m (DeepRepr a)
  toDeepRepr (Mon m) = m (Return . toDeepRepr)
  fromDeepRepr m = Mon $ \k -> Bind m (k . fromDeepRepr)
  {-
  -- a potential optimization?
  fromDeepRepr (m :: Fuzzi (_ (DeepRepr a))) =
    case ( eqTypeRep (typeRep @(DeepRepr a)) (typeRep @(()))
         , eqTypeRep (typeRep @a) (typeRep @(()))) of
      (Just HRefl, Just HRefl) ->
        Mon $ \k -> Sequence m (k ())
      _ ->
        Mon $ \k -> Bind m (k . fromDeepRepr)
  -}

instance (Monad m, Typeable m) => Syntactic1 (Mon m) where
  type DeepRepr1 (Mon m) = m
  toDeepRepr1 (Mon m) = m (Return . toDeepRepr)
  fromDeepRepr1 m = Mon $ \k -> Bind m (k . fromDeepRepr)

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

instance (IntNumeric a) => LiteIntegral (Fuzzi a) where
  idiv = IDiv
  imod = IMod

instance ( Boolean (Fuzzi (CmpResult a))
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
