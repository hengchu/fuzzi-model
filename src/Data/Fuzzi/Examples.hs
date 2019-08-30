module Data.Fuzzi.Examples where

import Data.Fuzzi.Interface
import qualified Data.Set as S
import Data.Fuzzi.Types

ex1 :: (FuzziLang m a) => Mon m (Fuzzi a)
ex1 = do
  x1 <- lap 1.0 1.0
  x2 <- lap 2.0 1.0
  return $ x1 + x2

ex2 :: (FuzziLang m a) => Mon m (Fuzzi a)
ex2 = do
  x1 <- lap 1.0 1.0
  x2 <- lap x1 1.0
  return $ x1 + x2

ex3 :: Fuzzi Double -> Fuzzi Double -> Fuzzi Double
ex3 a b = if_ (a %> b) a b

ex4 :: (FuzziLang m a, ConcreteBoolean (CmpResult a)) => Mon m (Fuzzi a)
ex4 = do
  x1 <- lap 1.0 1.0
  x2 <- lap 1.0 1.0
  ifM (x1 %> x2)
      (do x3 <- gauss 1.0 1.0
          return $ if_ (x3 %> x1) x3 x1
      )
      (do x4 <- gauss 1.0 1.0
          return $ if_ (x4 %> x2) x4 x2
      )

reportNoisyMaxAux :: (FuzziLang m a)
                  => [Fuzzi a]
                  -> Fuzzi Int
                  -> Fuzzi Int
                  -> Fuzzi a
                  -> Mon m (Fuzzi Int)
reportNoisyMaxAux []     _       maxIdx _       = return maxIdx
reportNoisyMaxAux (xNoised:xs) lastIdx maxIdx currMax = do
  let thisIdx = lastIdx + 1
  ifM (xNoised %> currMax)
      (reportNoisyMaxAux xs thisIdx thisIdx xNoised)
      (reportNoisyMaxAux xs thisIdx maxIdx  currMax)

reportNoisyMax :: forall m a.
                  (FuzziLang m a)
               => [Fuzzi a]
               -> Mon m (Fuzzi Int)
reportNoisyMax []     = error "reportNoisyMax received empty input"
reportNoisyMax (x:xs) = do
  xNoised <- lap x 1.0
  xsNoised <- mapM (`lap` 1.0) xs
  reportNoisyMaxAux xsNoised 0 0 xNoised

reportNoisyMaxBuggy :: forall m a.
                       (FuzziLang m a)
                    => [Fuzzi a]
                    -> Mon m (Fuzzi Int)
reportNoisyMaxBuggy []     = error "reportNoisyMaxBuggy received empty input"
reportNoisyMaxBuggy (x:xs) = do
  xNoised <- lap x 1.0
  xsNoised <- mapM (`lap` 1.0) xs
  reportNoisyMaxAux xs 0 0 x

smartSumAux :: ( FuzziLang m a
               , ListLike listA
               , Elem listA ~ a
               , FuzziType listA
               , FuzziType (LengthResult listA)
               , Numeric (LengthResult listA)
               , ConcreteBoolean (TestResult listA))
            => [Fuzzi a] -- ^The inputs
            -> Fuzzi a   -- ^The next partial sum
            -> Fuzzi a   -- ^This partial sum
            -> Fuzzi Int -- ^Iteration index
            -> Fuzzi a   -- ^The un-noised raw sum
            -> Fuzzi listA -- ^The accumulated list
            -> Mon m (Fuzzi listA)
smartSumAux []     _    _ _ _   results = return results
smartSumAux (x:xs) next n i sum results = do
  let sum' = sum + x
  if_ (((i + 1) `imod` 2) %== 0)
      (do n' <- lap (n + sum') 1.0
          smartSumAux xs n'    n' (i+1) 0    (results `snoc` n'))
      (do next' <- lap (next + x) 1.0
          smartSumAux xs next' n  (i+1) sum' (results `snoc` next'))

smartSumAuxBuggy :: ( FuzziLang m a
                    , ListLike listA
                    , Elem listA ~ a
                    , FuzziType listA
                    , FuzziType (LengthResult listA)
                    , Numeric (LengthResult listA)
                    , ConcreteBoolean (TestResult listA))
                 => [Fuzzi a] -- ^The inputs
                 -> Fuzzi a   -- ^The next partial sum
                 -> Fuzzi a   -- ^This partial sum
                 -> Fuzzi Int -- ^Iteration index
                 -> Fuzzi a   -- ^The un-noised raw sum
                 -> Fuzzi listA -- ^The accumulated list
                 -> Mon m (Fuzzi listA)
smartSumAuxBuggy []     _    _ _ _   results = return results
smartSumAuxBuggy (x:xs) next n i sum results = do
  let sum' = sum + x
  if_ (((i + 1) `imod` 2) %== 0)
      (do n' <- lap (n + sum') 1.0
          smartSumAuxBuggy xs n'    n' (i+1) sum' (results `snoc` n'))    -- here's the bug
      (do next' <- lap (next + x) 1.0
          smartSumAuxBuggy xs next' n  (i+1) sum' (results `snoc` next'))

smartSum :: forall m a listA.
            ( FuzziLang m a
            , ListLike listA
            , Elem listA ~ a
            , FuzziType listA
            , FuzziType (LengthResult listA)
            , Numeric (LengthResult listA)
            , ConcreteBoolean (TestResult listA))
         => [Fuzzi a]
         -> Mon m (Fuzzi listA)
-- smartSum :: forall m a listA. _ => [Fuzzi a] -> Mon m (Fuzzi listA)
smartSum xs = smartSumAux xs 0 0 0 0 nil

smartSumBuggy :: forall m a listA.
                 ( FuzziLang m a
                 , ListLike listA
                 , Elem listA ~ a
                 , FuzziType listA
                 , FuzziType (LengthResult listA)
                 , Numeric (LengthResult listA)
                 , ConcreteBoolean (TestResult listA))
              => [Fuzzi a]
              -> Mon m (Fuzzi listA)
-- smartSumBuggy :: forall m a listA. _ => [Fuzzi a] -> Mon m (Fuzzi listA)
smartSumBuggy xs = smartSumAuxBuggy xs 0 0 0 0 nil

sparseVector :: ( FuzziLang m a
                , ListLike  listBool
                , Elem      listBool ~ Bool
                , FuzziType listBool
                , FuzziType (LengthResult listBool)
                , Numeric (LengthResult listBool)
                , ConcreteBoolean (TestResult listBool))
             => [Fuzzi a] -- ^ input data
             -> Int       -- ^ maximum number of above thresholds
             -> Fuzzi a   -- ^ threshold
             -> Mon m (Fuzzi listBool)
sparseVector xs n threshold = do
  noisedThreshold <- lap threshold 2.0
  noisedXs <- mapM (`lap` (4.0 * fromIntegral n)) xs
  sparseVectorAux noisedXs n noisedThreshold nil

sparseVectorAux :: ( FuzziLang m a
                   , ListLike  listBool
                   , Elem      listBool ~ Bool
                   , FuzziType listBool
                   , FuzziType (LengthResult listBool)
                   , Numeric (LengthResult listBool)
                   , ConcreteBoolean (TestResult listBool)
                   )
                => [Fuzzi a]
                -> Int
                -> Fuzzi a
                -> Fuzzi listBool
                -> Mon m (Fuzzi listBool)
sparseVectorAux []     n threshold acc = return acc
sparseVectorAux (x:xs) n threshold acc
  | n <= 0    = return acc
  | otherwise = do
      ifM (x %> threshold)
          (sparseVectorAux xs (n-1) threshold (acc `snoc` lit True))
          (sparseVectorAux xs n     threshold (acc `snoc` lit False))

sparseVectorBuggy :: ( FuzziLang m a
                     , ListLike  listA
                     , Elem      listA ~ a
                     , FuzziType listA
                     , FuzziType (LengthResult listA)
                     , Numeric (LengthResult listA)
                     , ConcreteBoolean (TestResult listA))
                  => [Fuzzi a] -- ^ input data
                  -> Int       -- ^ maximum number of above thresholds
                  -> Fuzzi a   -- ^ threshold
                  -> Mon m (Fuzzi listA)
sparseVectorBuggy xs n threshold = do
  noisedThreshold <- lap threshold 2.0
  noisedXs <- mapM (`lap` (4.0 * fromIntegral n)) xs
  sparseVectorBuggyAux noisedXs n noisedThreshold nil

sparseVectorBuggyAux :: ( FuzziLang m a
                        , ListLike  listA
                        , Elem      listA ~ a
                        , FuzziType listA
                        , FuzziType (LengthResult listA)
                        , Numeric (LengthResult listA)
                        , ConcreteBoolean (TestResult listA)
                        )
                     => [Fuzzi a]
                     -> Int
                     -> Fuzzi a
                     -> Fuzzi listA
                     -> Mon m (Fuzzi listA)
sparseVectorBuggyAux []     n threshold acc = return acc
sparseVectorBuggyAux (x:xs) n threshold acc
  | n <= 0    = return acc
  | otherwise = do
      ifM (x %> threshold)
          (sparseVectorBuggyAux xs (n-1) threshold (acc `snoc` x))
          (sparseVectorBuggyAux xs n     threshold (acc `snoc` 0))

k_PT_LAMBDA :: (Fractional a) => a
k_PT_LAMBDA = 1.0

k_PT_GAMMA :: (Fractional a) => a
k_PT_GAMMA = 1.0

k_PT_DELTA :: (Fractional a) => a
k_PT_DELTA = k_PT_LAMBDA * k_PT_GAMMA

k_PT_THRESHOLD :: (Fractional a) => a
k_PT_THRESHOLD = 2

privTree :: (FuzziLang m a) => [Double] -> Mon m (Fuzzi (PrivTree1D a))
privTree xs =
  privTreeAux xs [rootNode] (S.singleton rootNode) (lit emptyTree)

privTreeAux :: forall m a.
               (FuzziLang m a)
            => [Double]                     -- ^input points on the unit interval
            -> [PrivTreeNode1D]             -- ^queue of unvisited nodes
            -> S.Set PrivTreeNode1D         -- ^current set of leaf nodes
            -> Fuzzi (PrivTree1D a)         -- ^current tree
            -> Mon m (Fuzzi (PrivTree1D a))
privTreeAux points queue leafNodes tree
  | length leafNodes > length points
  = abort "unreachable code: there are more leaf nodes than points"
  | otherwise
  = case queue of
      [] -> return tree
      (thisNode:more) -> do
        let biasedCount = countPoints points thisNode - depth thisNode * k_PT_DELTA
        biasedCount' <-
          ifM (biasedCount %> (k_PT_THRESHOLD - k_PT_DELTA))
              (return biasedCount)
              (return $ k_PT_THRESHOLD - k_PT_DELTA)
        noisedBiasedCount <- lap biasedCount' k_PT_LAMBDA
        let updatedTree = updatePT (lit thisNode) noisedBiasedCount tree
        ifM (noisedBiasedCount %> k_PT_THRESHOLD)
            (do let (left, right) = split thisNode
                let leafNodes' =
                      S.insert right (S.insert left (S.delete thisNode leafNodes))
                privTreeAux points (more++[left,right]) leafNodes' updatedTree
            )
            (privTreeAux
               points
               more
               leafNodes
               updatedTree)
