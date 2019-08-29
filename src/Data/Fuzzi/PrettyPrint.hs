module Data.Fuzzi.PrettyPrint where

import Data.Text (Text)
import Prelude hiding ((<>))
import Control.Lens
import Control.Monad.State.Strict
import Data.Fuzzi.EDSL
import Text.PrettyPrint
import qualified Data.Map.Strict as M

{- HLINT ignore "Reduce duplication" -}

type NameMap = M.Map String Int
newtype PrettyPrintState = PrettyPrintState {
  _ppsNameMap :: NameMap
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''PrettyPrintState

newtype PrettyPrintM a = PrettyPrintM {
  runPrettyPrintM :: State PrettyPrintState a
} deriving (Functor, Applicative, Monad, MonadState PrettyPrintState)
  via (State PrettyPrintState)

data SomeFuzzi :: * where
  MkSomeFuzzi :: Fuzzi a -> SomeFuzzi

instance Show SomeFuzzi where
  show = prettySomeFuzzi

instance Eq SomeFuzzi where
  a == b = show a == show b

instance Ord SomeFuzzi where
  compare a b = compare (show a) (show b)

prettySomeFuzzi :: SomeFuzzi -> String
prettySomeFuzzi (MkSomeFuzzi a) = render $ runPrettyPrint (pretty a)

runPrettyPrint :: PrettyPrintM a -> a
runPrettyPrint = flip evalState (PrettyPrintState M.empty) . runPrettyPrintM

commaSep :: Doc -> Doc -> Doc
commaSep a b = a <> comma <+> b

globalFreshVar :: String -> PrettyPrintM String
globalFreshVar hint = do
  names <- gets (^. nameMap)
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
pretty (Sequence a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ vcat [ a'
                , b'
                ]
pretty (Bind a@Laplace{} f) = do
  a' <- pretty a
  fv <- globalFreshVar "lap"
  f' <- pretty (f (PrettyPrintVariable fv))
  return $ vcat [
    text fv <+> text "<-" <+> a'
    , f'
    ]
pretty (Bind a@Gaussian{} f) = do
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
pretty (AssertTrueM cond) = do
  cond' <- pretty cond
  return $ text "assertTrue" <+> cond'
pretty (AssertFalseM cond) = do
  cond' <- pretty cond
  return $ text "assertFalse" <+> cond'
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
pretty (ListLength xs) = do
  xs' <- pretty xs
  return $ hsep [text "length", xs']
pretty (ListFilter f xs) = do
  f' <- pretty f
  xs' <- pretty xs
  return $ hsep [text "filter", f', xs']
pretty (Pair a b) = do
  a' <- pretty a
  b' <- pretty b
  return $ parens (a' `commaSep` b')
pretty (Fst p) = do
  p' <- pretty p
  return $ text "fst" <+> p'
pretty (Snd p) = do
  p' <- pretty p
  return $ text "snd" <+> p'
pretty (NumCast x) = do
  x' <- pretty x
  return $ hsep [text "fromIntegral", x']
pretty EmptyPrivTree = return (text "emptyPrivTree")
pretty (SplitPrivTreeNode node) = do
  node' <- pretty node
  return $ hsep [text "split", node']
pretty (UpdatePrivTree node value tree) = do
  node' <- pretty node
  value' <- pretty value
  tree' <- pretty tree
  return $ hsep [text "update", node', value', tree']
pretty (CountPointsPrivTree points node) = do
  node' <- pretty node
  points' <- pretty points
  return $ hsep [text "countPoints", points', node']
pretty (DepthPrivTree node tree) = do
  node' <- pretty node
  tree' <- pretty tree
  return $ hsep [text "depth", node', tree']

precedence :: M.Map Text Int
precedence = M.fromList [("||", 0), ("&&", 1),
                         ("==", 2),
                         ("<", 3), ("<=", 3), (">", 3), (">=", 3),
                         ("+", 4), ("-", 4), ("*", 5), ("/", 5)
                        ]

fixity :: M.Map Text Int
fixity = M.fromList [("||", 0), ("&&", 1),
                     ("==", 0),
                     ("<", 0), ("<=", 0), (">", 0), (">=", 0),
                     ("+", 1), ("-", 1), ("*", 1), ("/", 1)
                    ]
