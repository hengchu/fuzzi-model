module PrettyPrint where

import Prelude hiding ((<>))
import Control.Lens
import Control.Monad.State.Strict
import EDSL
import Text.PrettyPrint
import qualified Data.Map.Strict as M

type NameMap = M.Map String Int
data PrettyPrintState = PrettyPrintState {
  _ppsNameMap :: NameMap
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''PrettyPrintState

newtype PrettyPrintM a = PrettyPrintM {
  runPrettyPrintM :: State PrettyPrintState a
} deriving (Functor, Applicative, Monad, MonadState PrettyPrintState)
  via (State PrettyPrintState)

runPrettyPrint :: PrettyPrintM a -> a
runPrettyPrint = (flip evalState (PrettyPrintState M.empty)) . runPrettyPrintM

globalFreshVar :: String -> PrettyPrintM String
globalFreshVar hint = do
  names <- gets (\st -> st ^. nameMap)
  case M.lookup hint names of
    Nothing -> do
      modify (\st -> st & nameMap %~ M.insert hint 1)
      return hint
    Just nextIdx -> do
      modify (\st -> st & nameMap %~ M.insert hint (nextIdx + 1))
      return (hint ++ show nextIdx)

pretty :: Fuzzi a -> PrettyPrintM Doc
pretty (Variable x) = error $ "unexpected variable: " ++ show x
pretty (PrettyPrintVariable x) = return (text x)
pretty (Lam f) = do
  fv <- globalFreshVar "x"
  f' <- pretty (f (PrettyPrintVariable fv))
  -- \x -> f
  return $ char '\\' <> text fv <+> text "->" <+> f'
pretty (App f a) = do
  f' <- pretty f
  a' <- pretty a
  return (f' <+> a')
pretty (Return a) = do
  a' <- pretty a
  return (text "ret" <+> a')
pretty (Bind a@(Laplace _ _ _) f) = do
  a' <- pretty a
  fv <- globalFreshVar "lap"
  f' <- pretty (f (PrettyPrintVariable fv))
  return $ vcat [
    text fv <+> text "<-" <+> a'
    , f'
    ]
pretty (Bind a@(Gaussian _ _ _) f) = do
  a' <- pretty a
  fv <- globalFreshVar "gauss"
  f' <- pretty (f (PrettyPrintVariable fv))
  return $ vcat [
    text fv <+> text "<-" <+> a'
    , f'
    ]
pretty (Bind a f) = do
  a' <- pretty a
  fv <- globalFreshVar "x"
  f' <- pretty (f (PrettyPrintVariable fv))
  return $ vcat [
    text fv <+> text "<-" <+> a'
    , f'
    ]
pretty (Lit v) = return (text (show v))
pretty (If cond t f) = do
  cond' <- pretty cond
  t' <- pretty t
  f' <- pretty f
  return $ hsep [ text "if", cond', text "then", t', text "else", f' ]
pretty (IfM cond t f) = do
  cond' <- pretty cond
  t' <- pretty t
  f' <- pretty f
  return $ vcat [
    text "ifM" <+> cond',
    text "then",
    nest 2 t',
    text "else",
    nest 2 f'
    ]
pretty (Laplace _ c w) = do
  c' <- pretty c
  return $ hsep [ text "lap", c', double w ]
pretty (Gaussian _ c w) = do
  c' <- pretty c
  return $ hsep [ text "gauss", c', double w ]
pretty (And a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "&&", b']
pretty (Or a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "||", b']
pretty (Not a) = do
  a' <- pretty a
  return $ hsep [text "not", a']
pretty (Add a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "+", b']
pretty (Mult a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "*", b']
pretty (Sub a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "-", b']
pretty (Sign a) = do
  a' <- pretty a
  return $ hsep [text "sign", a']
pretty (Abs a) = do
  a' <- pretty a
  return $ hsep [text "abs", a']
pretty (Div a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "/", b']
pretty (IDiv a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "//", b']
pretty (IMod a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "%", b']
pretty (Lt a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "<", b']
pretty (Le a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "<=", b']
pretty (Gt a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text ">", b']
pretty (Ge a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text ">=", b']
pretty (Eq_ a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "==", b']
pretty (Neq a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ hsep [a', text "/=", b']
pretty (AssertTrueM cond k) = do
  cond' <- pretty cond
  k' <- pretty k
  return $ vcat [ text "assertTrue" <+> cond'
                , k'
                ]
pretty (AssertFalseM cond k) = do
  cond' <- pretty cond
  k' <- pretty k
  return $ vcat [ text "assertFalse" <+> cond'
                , k'
                ]

pretty (InjectProvenance a) = do
  a' <- pretty a
  return $ hsep [ text "injectProvenance", a' ]
pretty ListNil = return (text "[]")
pretty (ListCons x xs) = do
  x' <- pretty x
  xs' <- pretty xs
  return $ hsep [x', text ":", xs']
pretty (ListSnoc xs x) = do
  xs' <- pretty xs
  x' <- pretty x
  return $ hsep [text "snoc", xs', x']
pretty (ListIsNil xs) = do
  xs' <- pretty xs
  return $ hsep [text "isNil", xs']
