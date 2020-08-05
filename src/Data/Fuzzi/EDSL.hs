{-# OPTIONS_HADDOCK prune #-}
{-# LANGUAGE DerivingVia #-}
{-|
Module: Data.Fuzzi.EDSL
Description: The *internal* definitions of program syntax. Users do not need these internals to use this library.
-}
module Data.Fuzzi.EDSL (
  Fuzzi(..)
  , Syntactic
  , Syntactic1
  , Mon

  , if_
  , ifM
  , lap
  , geo
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
  , isJust_
  , fromJust_
  , isNil
  , uncons
  , fromIntegral_
  , reify
  , streamline
  , loop
  ) where

import Data.Coerce
import Type.Reflection (Typeable, typeRep, eqTypeRep, (:~~:)(..))
import Data.Fuzzi.Types hiding (SymbolicExpr(..))
import Control.Monad.Catch
import Data.Fuzzi.IfCxt

-- |A type for shallowly embedding monadic code
newtype Mon m a = Mon { runMon :: forall b. (FuzziType b) => (a -> Fuzzi (m b)) -> Fuzzi (m b) }
  deriving (Functor)

-- |The main typeclass for reification and reflection.
class Typeable (DeepRepr a) => Syntactic a where
  type DeepRepr a :: *
  -- |Convert a shallowly embedded program to its deep representation.
  toDeepRepr      :: a -> Fuzzi (DeepRepr a)

  -- |Convert the deep representation of a program to its shallow representation.
  fromDeepRepr    :: Fuzzi (DeepRepr a) -> a

-- |A typeclass for converting programs between deep and shallow representation
class Syntactic1 (m :: * -> *) where
  type DeepRepr1 m :: * -> *
  toDeepRepr1   :: (Syntactic a, FuzziType (DeepRepr a)) => m a -> Fuzzi (DeepRepr1 m (DeepRepr a))
  fromDeepRepr1 :: (Syntactic a, FuzziType (DeepRepr a)) => Fuzzi (DeepRepr1 m (DeepRepr a)) -> m a

-- |The deep representation of a program
data Fuzzi (a :: *) where
  Lam         :: (FuzziType a, FuzziType b) => (Fuzzi a -> Fuzzi b) -> Fuzzi (a -> b)
  App         :: (FuzziType a, FuzziType b) => Fuzzi (a -> b) -> Fuzzi a -> Fuzzi b

  Return      :: (Monad m, FuzziType a) => Fuzzi a -> Fuzzi (m a)
  Sequence    :: (Monad m, Typeable m, FuzziType a) => Fuzzi (m ()) -> Fuzzi (m a) -> Fuzzi (m a)
  Bind        :: (Monad m, Typeable m, FuzziType a, FuzziType b) => Fuzzi (m a) -> (Fuzzi a -> Fuzzi (m b)) -> Fuzzi (m b)
  Lit         :: (FuzziType a) => a -> Fuzzi a
  If          :: (FuzziType bool, IfCxt (ConcreteBoolean bool)) => Fuzzi bool -> Fuzzi a -> Fuzzi a -> Fuzzi a
  IfM         :: (FuzziType a, Assertion m bool) => Fuzzi bool -> Fuzzi (m a) -> Fuzzi (m a) -> Fuzzi (m a)
  Laplace     :: (Distribution m a) =>             Fuzzi a -> Fuzzi a -> Fuzzi (m a)
  Laplace'    :: (Distribution m a) => Rational -> Fuzzi a -> Fuzzi a -> Fuzzi (m a)
  Geometric   :: (Distribution' m int real, FractionalOf int ~ real) => Fuzzi int -> Fuzzi real -> Fuzzi (m int)
  Gaussian    :: (Distribution m a) =>             Fuzzi a -> Double -> Fuzzi (m a)
  Gaussian'   :: (Distribution m a) => Rational -> Fuzzi a -> Double -> Fuzzi (m a)
  Variable    :: (Typeable a) => Int -> Fuzzi a

  Loop :: (Monad m, FuzziType acc, FuzziType bool, ConcreteBoolean bool)
       => Fuzzi acc                    -- ^loop accumulator
       -> (Fuzzi acc -> Fuzzi bool)    -- ^loop condition
       -> (Fuzzi acc -> Fuzzi (m acc)) -- ^loop iteration
       -> Fuzzi (m acc)

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
  FExp        :: (FloatNumeric a) => Fuzzi a -> Fuzzi a

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
  ListUncons :: (FuzziType a) => Fuzzi [a] -> Fuzzi (Maybe (a, [a]))

  Just_      :: (FuzziType a) => Fuzzi a -> Fuzzi (Maybe a)
  Nothing_   :: (FuzziType a) => Fuzzi (Maybe a)
  IsJust_    :: (FuzziType a, FuzziType bool, ConcreteBoolean bool) => Fuzzi (Maybe a) -> Fuzzi bool
  FromJust_  :: (FuzziType a) => Fuzzi (Maybe a) -> Fuzzi a

  Pair      :: (FuzziType a, FuzziType b) => Fuzzi a -> Fuzzi b      -> Fuzzi (a, b)
  Fst       :: (FuzziType a, FuzziType b) =>            Fuzzi (a, b) -> Fuzzi a
  Snd       :: (FuzziType a, FuzziType b) =>            Fuzzi (a, b) -> Fuzzi b

  NumCast   :: (FuzziType a, FuzziType b, Integral a, Num b) => Fuzzi a -> Fuzzi b

  Abort     :: (FuzziType a, Typeable m, MonadThrow m) => String -> Fuzzi (m a)

  UpdatePrivTree :: (FuzziType a) => Fuzzi PrivTreeNode1D -> Fuzzi a -> Fuzzi (PrivTree1D a) -> Fuzzi (PrivTree1D a)

-- |Creates an optional value that is 'Just' something.
just :: (FuzziType a) => Fuzzi a -> Fuzzi (Maybe a)
just = Just_

-- |Creates an optional value that does not contain anything.
nothing :: (FuzziType a) => Fuzzi (Maybe a)
nothing = Nothing_

-- |Unwraps an optional value, extracting the contained 'Just' value, crashes if
-- the optional value is 'Nothing'.
fromJust_ :: (FuzziType a) => Fuzzi (Maybe a) -> Fuzzi a
fromJust_ = FromJust_

-- |Tests if an optional value is 'Just' something.
isJust_ :: (FuzziType a, FuzziType bool, ConcreteBoolean bool) => Fuzzi (Maybe a) -> Fuzzi bool
isJust_ = IsJust_

-- |Empty list.
nil :: (FuzziType a) => Fuzzi [a]
nil = ListNil

-- |List cons.
cons :: (FuzziType a) => Fuzzi a -> Fuzzi [a] -> Fuzzi [a]
cons = ListCons

-- |List append.
snoc :: (FuzziType a) => Fuzzi [a] -> Fuzzi a -> Fuzzi [a]
snoc = ListSnoc

-- |Tests if a list is empty.
isNil :: (FuzziType a, ConcreteBoolean bool) => Fuzzi [a] -> Fuzzi bool
isNil = ListIsNil

-- |Split a non-empty list into head and tail, crashes if list is empty.
uncons :: (FuzziType a) => Fuzzi [a] -> Fuzzi (Maybe (a, [a]))
uncons = ListUncons

--length_ :: (FuzziType a) => Fuzzi [a] -> Fuzzi Int
--length_ = ListLength

-- |Updates a privtree data structure.
updatePT :: (FuzziType a)
         => Fuzzi PrivTreeNode1D
         -> Fuzzi a
         -> Fuzzi (PrivTree1D a)
         -> Fuzzi (PrivTree1D a)
updatePT = UpdatePrivTree

-- |A "crash" statement, evaluation that hits this statement immediately
-- terminates.
abort :: ( FuzziType a
         , Typeable m
         , MonadThrow m
         ) => String -> Mon m (Fuzzi a)
abort reason = fromDeepRepr $ Abort reason

-- |Boolean true.
true :: Fuzzi Bool
true = Lit True

-- |Boolean false.
false :: Fuzzi Bool
false = Lit False

-- |Convert integral values into fractional values.
fromIntegral_ :: (FuzziType a, FuzziType b, Integral a, Num b) => Fuzzi a -> Fuzzi b
fromIntegral_ = NumCast

-- |Creates a control flow statement that branches on deterministic data.
if_ :: (Syntactic a, FuzziType bool, IfCxt (ConcreteBoolean bool)) => Fuzzi bool -> a -> a -> a
if_ c t f = fromDeepRepr $ If c (toDeepRepr t) (toDeepRepr f)

-- |Creates an explicit loop.
loop :: ( ConcreteBoolean bool
        , FuzziType bool
        , FuzziType (DeepRepr acc)
        , Syntactic acc
        , Syntactic1 m
        , Monad m
        , Monad (DeepRepr1 m)
        , Typeable m
        ) => acc -> (acc -> Fuzzi bool) -> (acc -> m acc) -> m acc
loop acc pred iter =
  fromDeepRepr1 $ Loop (toDeepRepr acc) (pred . fromDeepRepr) (toDeepRepr1 . iter . fromDeepRepr)

-- |Creates a control flow statement that may branch on probabilistic samples.
ifM :: ( Syntactic1 m
       , Syntactic a
       , Assertion (DeepRepr1 m) bool
       , FuzziType (DeepRepr a)) => Fuzzi bool -> m a -> m a -> m a
ifM c t f = fromDeepRepr1 $ IfM c (toDeepRepr1 t) (toDeepRepr1 f)

-- |Sampling instruction for a laplace distribution.
lap :: forall m a. Distribution m a => Fuzzi a -> Fuzzi a -> Mon m (Fuzzi a)
lap c w = fromDeepRepr $ Laplace c w -- Mon ((Bind (Laplace c w)))

-- |Sampling instruction for a two-sided geometric distribution.
geo :: forall m int real. (Distribution' m int real, FractionalOf int ~ real) => Fuzzi int -> Fuzzi real -> Mon m (Fuzzi int)
geo c alpha = fromDeepRepr $ Geometric c alpha

gauss :: forall m a. Distribution m a => Fuzzi a -> Double -> Mon m (Fuzzi a)
gauss c w = fromDeepRepr $ Gaussian c w --  Mon ((Bind (Gaussian c w)))

-- |Sampling instruction for a laplace distribution, while also specifying a
-- "tolerance" threshold for symbolic execution.
lap' :: forall m a. Distribution m a => Rational -> Fuzzi a -> Fuzzi a -> Mon m (Fuzzi a)
lap' tol c w = fromDeepRepr $ Laplace' tol c w -- Mon ((Bind (Laplace c w)))

gauss' :: forall m a. Distribution m a => Rational -> Fuzzi a -> Double -> Mon m (Fuzzi a)
gauss' tol c w = fromDeepRepr $ Gaussian' tol c w --  Mon ((Bind (Gaussian c w)))

-- |Creates a tuple.
pair :: (FuzziType a, FuzziType b) => Fuzzi a -> Fuzzi b -> Fuzzi (a, b)
pair = Pair

-- |Projects 1st value out of a tuple.
fst_ :: (FuzziType a, FuzziType b) => Fuzzi (a, b) -> Fuzzi a
fst_ = Fst

-- |Projects 2nd value out of a tuple.
snd_ :: (FuzziType a, FuzziType b) => Fuzzi (a, b) -> Fuzzi b
snd_ = Snd

-- |Injects a haskell value into the embedded program as a literal value.
lit :: (FuzziType a) => a -> Fuzzi a
lit = Lit

-- |Converts a shallowly embedded program into its deep representation.
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
    Laplace c w -> Laplace (subst v c filling) (subst v w filling)
    Geometric c a -> Geometric (subst v c filling) (subst v a filling)
    Gaussian c w -> Gaussian (subst v c filling) w
    Laplace' tol c w -> Laplace' tol (subst v c filling) (subst v w filling)
    Gaussian' tol c w -> Gaussian' tol (subst v c filling) w

    Loop acc pred iter -> Loop (subst v acc filling) (\x -> subst v (pred x) filling) (\x -> subst v (iter x) filling)

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

    Div  a b -> Div   (subst v a filling) (subst v b filling)
    IDiv a b -> IDiv  (subst v a filling) (subst v b filling)
    IMod a b -> IMod  (subst v a filling) (subst v b filling)
    FExp a   -> FExp  (subst v a filling)

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
    ListUncons xs -> ListUncons (subst v xs filling)

    Just_ x -> Just_ (subst v x filling)
    Nothing_ -> Nothing_
    FromJust_ x -> FromJust_ (subst v x filling)
    IsJust_ x -> IsJust_ (subst v x filling)

    NumCast a -> NumCast (subst v a filling)

    Pair a b -> Pair (subst v a filling) (subst v b filling)
    Fst p -> Fst (subst v p filling)
    Snd p -> Snd (subst v p filling)

    Abort reason -> Abort reason

    UpdatePrivTree node value tree ->
      UpdatePrivTree (subst v node filling) (subst v value filling) (subst v tree filling)

-- |Convert a program with conditionals into a list of all straightline single-path programs.
streamline :: Typeable a => Fuzzi a -> [Fuzzi a]
streamline = map optimize . streamlineAux 0 False

streamlineAux :: Typeable a => Int -> Bool -> Fuzzi a -> [Fuzzi a]
streamlineAux var inLoop (Lam (f :: Fuzzi x -> Fuzzi y)) =
  let bodies = streamlineAux (var + 1) inLoop (f (Variable var))
  in [Lam (subst @x var body) | body <- bodies]
streamlineAux var inLoop (App f a) =
  [App f' a' | f' <- streamlineAux var inLoop f, a' <- streamlineAux var inLoop a]
streamlineAux var inLoop (Return x) =
  [Return x' | x' <- streamlineAux var inLoop x]
streamlineAux var inLoop (Sequence a b) =
  [Sequence a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Bind a (f :: Fuzzi a -> Fuzzi (m b))) =
  let bodies = streamlineAux (var + 1) inLoop (f (Variable var))
  in [Bind a' (subst @a var body') | a' <- streamlineAux var inLoop a, body' <- bodies]
streamlineAux _ _ (Lit x) = [Lit x]
streamlineAux _var True If{} =
  error "streamline: cannot streamline branches in loop, use explicit recursion instead"
streamlineAux var False (If cond t f) =
  [If cond' t' f' | cond' <- streamlineAux var False cond,
   t' <- streamlineAux var False t, f' <- streamlineAux var False f]
streamlineAux _var True IfM{} =
  error "streamline: cannot streamline branches in loop, use explicit recursion instead"
streamlineAux var False (IfM cond t f) =
  let conds = streamlineAux var False cond
  in [Sequence (AssertTrueM cond') t' | cond' <- conds, t' <- streamlineAux var False t]
     ++ [Sequence (AssertFalseM cond') f' | cond' <- conds, f' <- streamlineAux var False f]
streamlineAux var inLoop (Geometric c a) =
  [Geometric c' a' | c' <- streamlineAux var inLoop c, a' <- streamlineAux var inLoop a]
streamlineAux var inLoop (Laplace c w) =
  [Laplace c' w' | c' <- streamlineAux var inLoop c, w' <- streamlineAux var inLoop w]
streamlineAux var inLoop (Gaussian c w) =
  [Gaussian c' w | c' <- streamlineAux var inLoop c]
streamlineAux var inLoop (Laplace' tol c w) =
  [Laplace' tol c' w' | c' <- streamlineAux var inLoop c, w' <- streamlineAux var inLoop w]
streamlineAux var inLoop (Gaussian' tol c w) =
  [Gaussian' tol c' w | c' <- streamlineAux var inLoop c]
streamlineAux var inLoop (Loop (acc :: Fuzzi acc) pred iter) =
  let preds = streamlineAux (var + 1) inLoop (pred (Variable var))
      iters = streamlineAux (var + 1) True (iter (Variable var))
  in [ Loop acc' (subst @acc var pred') (subst @acc var iter')
     | acc' <- streamlineAux var True acc, pred' <- preds, iter' <- iters
     ]
streamlineAux _ _ v@(Variable _) = [v]
streamlineAux _ _ v@(PrettyPrintVariable _) = [v]
streamlineAux var inLoop (And a b) =
  [And a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Or  a b) =
  [Or a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Not a) =
  [Not a' | a' <- streamlineAux var inLoop a]
streamlineAux var inLoop (Add a b) =
  [Add a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Mult a b) =
  [Mult a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Sub a b) =
  [Sub a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Sign a) =
  [Sign a' | a' <- streamlineAux var inLoop a]
streamlineAux var inLoop (Abs a) =
  [Abs a' | a' <- streamlineAux var inLoop a]
streamlineAux var inLoop (Div a b) =
  [Div a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (IDiv a b) =
  [IDiv a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (IMod a b) =
  [IMod a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (FExp a) =
  [FExp a' | a' <- streamlineAux var inLoop a]
streamlineAux var inLoop (Lt a b) =
  [Lt a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Le a b) =
  [Le a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Gt a b) =
  [Gt a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Ge a b) =
  [Ge a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Eq_ a b) =
  [Eq_ a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Neq a b) =
  [Neq a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (AssertTrueM cond) =
  [AssertTrueM cond' | cond' <- streamlineAux var inLoop cond]
streamlineAux var inLoop (AssertFalseM cond) =
  [AssertFalseM cond' | cond' <- streamlineAux var inLoop cond]
streamlineAux _ _ ListNil = [ListNil]
streamlineAux var inLoop (ListCons x xs) =
  [ListCons x' xs' | x' <- streamlineAux var inLoop x, xs' <- streamlineAux var inLoop xs]
streamlineAux var inLoop (ListSnoc xs x) =
  [ListSnoc xs' x' | xs' <- streamlineAux var inLoop xs, x' <- streamlineAux var inLoop x]
streamlineAux var inLoop (ListIsNil x) =
  [ListIsNil x' | x' <- streamlineAux var inLoop x]
streamlineAux var inLoop (ListUncons x) =
  [ListUncons x' | x' <- streamlineAux var inLoop x]
streamlineAux var inLoop (Pair a b) =
  [Pair a' b' | a' <- streamlineAux var inLoop a, b' <- streamlineAux var inLoop b]
streamlineAux var inLoop (Fst p) =
  Fst <$> streamlineAux var inLoop p
streamlineAux var inLoop (Snd p) =
  Snd <$> streamlineAux var inLoop p
streamlineAux var inLoop (NumCast x) =
  NumCast <$> streamlineAux var inLoop x
streamlineAux _var _ (Abort reason) =
  [Abort reason]
streamlineAux var inLoop (UpdatePrivTree node value tree) =
  [UpdatePrivTree node' value' tree' | node' <- streamlineAux var inLoop node,
   value' <- streamlineAux var inLoop value,
   tree' <- streamlineAux var inLoop tree]
streamlineAux var inLoop (Just_ x) =
  Just_ <$> streamlineAux var inLoop x
streamlineAux _ _ Nothing_ =
  [Nothing_]
streamlineAux var inLoop (FromJust_ x) =
  FromJust_ <$> streamlineAux var inLoop x
streamlineAux var inLoop (IsJust_ x) =
  IsJust_ <$> streamlineAux var inLoop x

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

instance (FuzziType a, FracNumeric a, FloatNumeric a) => LiteFloating (Fuzzi a) where
  fexp = FExp

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
