module Spec.Types.Structures where

import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.Coerce
import Data.Fuzzi.Logging
import Data.Fuzzi.Types
import Data.Fuzzi.Z3
import Data.Text (pack)
import Prelude hiding (and, or)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import qualified Data.Map.Strict as M
import qualified Z3.Base as Z3

newtype AnyIO m = AnyIO { runAnyIO :: m Bool }
newtype AllIO m = AllIO { runAllIO :: m Bool }

instance MonadIO m => Monoid (AllIO m) where
  mempty = AllIO $ return True

instance MonadIO m => Semigroup (AllIO m) where
  ma <> mb = AllIO $ do
    r <- runAllIO ma
    if r
      then runAllIO mb
      else return False

instance MonadIO m => Monoid (AnyIO m) where
  mempty = AnyIO $ return False

instance MonadIO m => Semigroup (AnyIO m) where
  ma <> mb = AnyIO $ do
    r <- runAnyIO ma
    if r
      then return True
      else runAnyIO mb

subset :: SEq a b => BoolExpr -> GuardedSymbolicUnion a -> GuardedSymbolicUnion b -> IO Bool
subset cond small large = runStdoutColoredLoggingWarnT $ subset' cond (unwrap small) (unwrap large)

checkImplicationAndEquality :: (SEq a b, MonadIO m, MonadLogger m)
                            => Z3.Context
                            -> Z3.Solver
                            -> BoolExpr
                            -> BoolExpr
                            -> a
                            -> BoolExpr
                            -> b
                            -> AnyIO m
checkImplicationAndEquality cxt solver cond smallCond smallValue largeCond largeValue =
  AnyIO $ do
    liftIO $ Z3.solverReset cxt solver
    let equalitySExpr = smallValue `symEq` largeValue
    let clause = (neg (cond `and` largeCond)) `or` (smallCond `and` equalitySExpr)
    formula <- flip runReaderT M.empty $ symbolicExprToZ3AST cxt . getBoolExpr $ clause
    liftIO $ Z3.solverAssertCnstr cxt solver formula
    $(logInfo) (pack . show $ "cond = " ++ show cond)
    $(logInfo) (pack . show $ "smallCond = " ++ show smallCond)
    $(logInfo) (pack . show $ "largeCond = " ++ show largeCond)
    $(logInfo) (pack . show $ "equaity = " ++ show equalitySExpr)
    let logMsg = "checking " ++ show cond ++ " /\\ " ++ show largeCond ++ " ==> " ++ show smallCond ++ " /\\ " ++ show equalitySExpr
    $(logInfo) (pack logMsg)
    r <- liftIO $ Z3.solverCheck cxt solver
    $(logInfo) (pack $ show "result = " ++ show r)
    case r of
      Z3.Sat -> return True
      _      -> return False

subset' :: forall m a b.
           ( SEq a b
           , MonadIO m
           , MonadLogger m
           ) => BoolExpr -> [Guarded a] -> [Guarded b] -> m Bool
subset' cond small large = do
  (cxt, solver) <- z3Init
  runAllIO $ foldMap (AllIO . forEachSmall cxt solver) small
  where forEachSmall :: Z3.Context -> Z3.Solver -> Guarded a -> m Bool
        forEachSmall cxt solver (MkGuarded smallCond smallValue) = runAnyIO $
          foldMap (\(MkGuarded largeCond largeValue) ->
                     checkImplicationAndEquality
                       cxt solver cond smallCond smallValue largeCond largeValue)
                  large

newtype SimpleSRealAtom = SimpleSRealAtom RealExpr
  deriving (Show, Eq, Ord)

newtype SimpleBoolAtom = SimpleBoolAtom BoolExpr
  deriving (Show, Eq, Ord)

atom2expr :: SimpleSRealAtom -> SimpleRealExpr
atom2expr (SimpleSRealAtom s) = SimpleRealExpr s

atom2bool :: SimpleBoolAtom -> SimpleBoolExpr
atom2bool (SimpleBoolAtom b) = SimpleBoolExpr b

expr2sexpr :: SimpleRealExpr -> (Rational, SymbolicExpr)
expr2sexpr (SimpleRealExpr s) = (getTolerance s, getRealExpr s)

bexpr2sexpr :: SimpleBoolExpr -> SymbolicExpr
bexpr2sexpr = coerce

rebuildReal :: Rational -> SymbolicExpr -> SimpleRealExpr
rebuildReal tol s = SimpleRealExpr (RealExpr tol s)

rebuildBool :: SymbolicExpr -> SimpleBoolExpr
rebuildBool = coerce

newtype SimpleRealExpr = SimpleRealExpr RealExpr
  deriving (Show, Eq, Ord)
  deriving (Num, Fractional, Ordered) via RealExpr

newtype SimpleBoolExpr = SimpleBoolExpr BoolExpr
  deriving (Show, Eq, Ord)
  deriving (Boolean) via BoolExpr

simpleAtomSet :: [SymbolicExpr]
simpleAtomSet = RealVar <$> ["s" ++ show i | i <- [0..9]]

instance Arbitrary SimpleSRealAtom where
  arbitrary = do
    idx <- elements [0..9]
    return . SimpleSRealAtom . sReal $ "s" ++ show idx
  shrink _ = []

instance Arbitrary SimpleBoolAtom where
  arbitrary = do
    realAtom <- atom2expr <$> arbitrary
    return (coerce $ realAtom %> 0)
  shrink _ = []

instance Arbitrary SimpleRealExpr where
  arbitrary =
    frequency [ --(6, atom2expr <$> arbitrary)
                (5, fromRational <$> elements [0..9])
              , (1, (+) <$> arbitrary <*> arbitrary)
              , (1, (*) <$> arbitrary <*> (fromRational <$> arbitrary))
              , (1, (*) <$> (fromRational <$> arbitrary) <*> arbitrary)
              , (1, (/) <$> arbitrary <*> (fromRational <$> arbitrary))
              ]
  shrink (expr2sexpr -> (_, Rat v)) = []
  shrink (expr2sexpr -> (_, RealVar _)) = []
  shrink (expr2sexpr -> (tol, lhs `Add` rhs)) =
    let ls = shrink (rebuildReal tol lhs)
        rs = shrink (rebuildReal tol rhs)
    in ls ++ rs ++ [l + r | l <- ls, r <- rs]
  shrink (expr2sexpr -> (tol, lhs `Sub` rhs)) =
    let ls = shrink (rebuildReal tol lhs)
        rs = shrink (rebuildReal tol rhs)
    in ls ++ rs ++ [l - r | l <- ls, r <- rs]
  shrink (expr2sexpr -> (tol, lhs `Mul` rhs)) =
    let ls = shrink (rebuildReal tol lhs)
        rs = shrink (rebuildReal tol rhs)
    in ls ++ rs ++ [l * r | l <- ls, r <- rs]
  shrink (expr2sexpr -> (tol, lhs `Div` rhs)) =
    let ls = shrink (rebuildReal tol lhs)
        rs = shrink (rebuildReal tol rhs)
    in ls ++ rs ++ [l / r | l <- ls, r <- rs]
  shrink s = error $ "shrink SimpleRealExpr: unexpected real expression " ++ show s

instance Arbitrary SimpleBoolExpr where
  arbitrary =
    frequency [ (10, atom2bool <$> arbitrary )
              , (1, and <$> arbitrary <*> arbitrary)
              , (1, or <$> arbitrary <*> arbitrary)
              , (1, neg <$> arbitrary)
              , (1, coerce $ ((%>) @SimpleRealExpr <$> arbitrary <*> arbitrary))
              , (1, coerce $ ((%>=) @SimpleRealExpr <$> arbitrary <*> arbitrary))
              , (1, coerce $ ((%<) @SimpleRealExpr <$> arbitrary <*> arbitrary))
              , (1, coerce $ ((%<=) @SimpleRealExpr <$> arbitrary <*> arbitrary))
              , (1, coerce $ ((%==) @SimpleRealExpr <$> arbitrary <*> arbitrary))
              , (1, coerce $ ((%/=) @SimpleRealExpr <$> arbitrary <*> arbitrary))
              ]
  shrink (bexpr2sexpr -> (JustBool r)) = coerce $ bool <$> shrink r
  shrink (bexpr2sexpr -> lhs `And` rhs) =
    let ls = coerce $ shrink (rebuildBool lhs)
        rs = coerce $ shrink (rebuildBool rhs)
    in ls ++ rs ++ [l `and` r | l <- ls, r <- rs]
  shrink (bexpr2sexpr -> lhs `Or` rhs) =
    let ls = coerce $ shrink (rebuildBool lhs)
        rs = coerce $ shrink (rebuildBool rhs)
    in ls ++ rs ++ [l `or` r | l <- ls, r <- rs]
  shrink (bexpr2sexpr -> (Not b)) =
    neg <$> shrink (rebuildBool b)
  shrink (bexpr2sexpr -> (lhs `Gt` rhs)) =
    let ls = shrink (rebuildReal k_FLOAT_TOLERANCE lhs)
        rs = shrink (rebuildReal k_FLOAT_TOLERANCE rhs)
    in (coerce $ (%> 0) <$> ls)
       ++ (coerce $ (%< 0) <$> rs)
       ++ [coerce (l %> r) | l <- ls, r <- rs]
  shrink (bexpr2sexpr -> (lhs `Ge` rhs)) =
    let ls = shrink (rebuildReal k_FLOAT_TOLERANCE lhs)
        rs = shrink (rebuildReal k_FLOAT_TOLERANCE rhs)
    in (coerce $ (%>= 0) <$> ls)
       ++ (coerce $ (%<= 0) <$> rs)
       ++ [coerce (l %>= r) | l <- ls, r <- rs]
  shrink (bexpr2sexpr -> (lhs `Lt` rhs)) =
    let ls = shrink (rebuildReal k_FLOAT_TOLERANCE lhs)
        rs = shrink (rebuildReal k_FLOAT_TOLERANCE rhs)
    in (coerce $ (%< 0) <$> ls)
       ++ (coerce $ (%> 0) <$> rs)
       ++ [coerce (l %< r) | l <- ls, r <- rs]
  shrink (bexpr2sexpr -> (lhs `Le` rhs)) =
    let ls = shrink (rebuildReal k_FLOAT_TOLERANCE lhs)
        rs = shrink (rebuildReal k_FLOAT_TOLERANCE rhs)
    in (coerce $ (%<= 0) <$> ls)
       ++ (coerce $ (%>= 0) <$> rs)
       ++ [coerce (l %<= r) | l <- ls, r <- rs]
  shrink (bexpr2sexpr -> (lhs `Eq_` rhs)) =
    let ls = shrink (rebuildReal k_FLOAT_TOLERANCE lhs)
        rs = shrink (rebuildReal k_FLOAT_TOLERANCE rhs)
    in [coerce (l %== r) | l <- ls, r <- rs]
  shrink b = error $ "shrink SimpleBoolExpr: unexpected bool expression" ++ show b

instance Arbitrary a => Arbitrary (GuardedSymbolicUnion a) where
  arbitrary = do
    condAndVal <- listOf1 ((,) <$> ((BoolExpr . bexpr2sexpr) <$> arbitrary) <*> arbitrary)
    return $ fromList condAndVal
  shrink (flatten -> []) = []
  shrink (flatten -> ((cond, v):rest)) =
    let singleton = fromList [(cond, v)]
        shrinkedSingletons :: _ =
          fromList <$> [ [(coerce cond', v')]
                       | cond' <- shrink (SimpleBoolExpr cond)
                       , v' <- shrink v
                       ]
        shrinkedRest = shrink (fromList rest) :: _
    in singleton:shrinkedSingletons ++ (union <$> shrinkedSingletons <*> shrinkedRest)

prop_mergeUnionResultIsSuperSet ::
  SimpleBoolExpr -> GuardedSymbolicUnion SimpleRealExpr -> GuardedSymbolicUnion SimpleRealExpr -> Property
prop_mergeUnionResultIsSuperSet (SimpleBoolExpr cond) s1 s2 = monadicIO $ do
  let
    s1' = fmap unwrapSimpleRealExpr s1
    s2' = fmap unwrapSimpleRealExpr s2
    u = mergeUnion cond s1' s2'
  r1 <- run $ subset cond s1' u
  assert r1
  r2 <- run $ subset (neg cond) s2' u
  assert r2
  where unwrapSimpleRealExpr (SimpleRealExpr s) = s

{-
Counterexample:

SimpleBoolExpr True

GuardedSymbolicUnion {unwrapGuardedSymbolicUnion = [MkGuarded (True) (SimpleRealExpr 247881476279982 % 5252571348565 * s7)]}

GuardedSymbolicUnion {unwrapGuardedSymbolicUnion = [MkGuarded (False) (SimpleRealExpr s3),MkGuarded (False) (SimpleRealExpr s3 / (-9335460263054) % 3931040545653),MkGuarded (True) (SimpleRealExpr s1),MkGuarded (74994466163271 % 1557401928167 * (s9 / 9639589846300 % 3148654066457) == s4) (SimpleRealExpr (s3 + s5) / 470506787888202 % 9626422663025 * (-71073912258251) % 3099006265195 / (-88722880018009) % 3874660982355),MkGuarded (True) (SimpleRealExpr s5),MkGuarded ((-115588470566914) % 2165963991753 < s4) (SimpleRealExpr s6),MkGuarded (38846926431767 % 1376199583946 * ((-208926744808755) % 3795756986822 * 11622766154953 % 632816602862) + s3 <= s5) (SimpleRealExpr (-180187412379527) % 6073835356312 * s3),MkGuarded (s0 < s7) (SimpleRealExpr s2)]}

SimpleBoolExpr False

GuardedSymbolicUnion {unwrapGuardedSymbolicUnion = [MkGuarded (True) (SimpleRealExpr (-3876293004456) % 258517669091 + s9)]}

GuardedSymbolicUnion {unwrapGuardedSymbolicUnion = [MkGuarded (s4 <= s8 * 21577907387655 % 8329232379602 * 268840737166 % 261914575513) (SimpleRealExpr s9)]}

symmetric diff is wrong, matchable instances are wrong, the two sides should
express the same set of values, right now, a constant 1 and a symbol s matches,
and it may cause s to be dropped and only keep s1

SimpleBoolExpr not(s7 == s0)
GuardedSymbolicUnion {unwrapGuardedSymbolicUnion = [MkGuarded (s2 > 0 % 1) (SimpleRealExpr s7)]}
GuardedSymbolicUnion {unwrapGuardedSymbolicUnion = [MkGuarded (s3 > 0 % 1) (SimpleRealExpr s6),MkGuarded (not(s2 + (-1447922192308) % 929748654031 == s8)) (SimpleRealExpr s4),MkGuarded (((-22598647323272) % 9322564761029 + s5 / 14406561909965 % 5435786934498) / 4610059516427 % 1175001968606 < s2) (SimpleRealExpr s7)]}

-}

{-
cond :: BoolExpr
cond = neg (sReal "s7" %== sReal "s0")

u1 :: GuardedSymbolicUnion RealExpr
u1 = guardedSingleton (sReal "s2" %> 0) (sReal "s7")

u2 :: GuardedSymbolicUnion RealExpr
u2 = fromList [ (sReal "s3" %> 0, sReal "s6")
              , (neg $ (sReal "s2" + 1) %== sReal "s8", sReal "s4")
              , (1 %< sReal "s2", sReal "s7")
              ]
-}

--cond = sReal "s8" %> 0
cond = bool True
u1 = guardedSingleton ((sReal "s9" %> 0) `or` (sReal "s3" %> 0)) (2 / (3 :: RealExpr))
u2 = guardedSingleton (4 %< (5 :: RealExpr)) (-1 * 2 :: RealExpr)
