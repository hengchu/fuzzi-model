module Data.Fuzzi.Examples where

import Data.Fuzzi.Interface
import qualified Data.Set as S

{- HLINT ignore "Use camelCase" -}

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
reportNoisyMaxAux []           _       maxIdx _       = return maxIdx
reportNoisyMaxAux (xNoised:xs) lastIdx maxIdx currMax = do
  let thisIdx = lastIdx + 1
  ifM (xNoised %> currMax)
      (reportNoisyMaxAux xs thisIdx thisIdx xNoised)
      (reportNoisyMaxAux xs thisIdx maxIdx  currMax)

reportNoisyMaxAuxOpt :: (FuzziLang m a, FuzziType int, Numeric int)
                     => [Fuzzi a]
                     -> Fuzzi int
                     -> Fuzzi int
                     -> Fuzzi a
                     -> Mon m (Fuzzi int)
reportNoisyMaxAuxOpt []           _       maxIdx _       = return maxIdx
reportNoisyMaxAuxOpt (xNoised:xs) lastIdx maxIdx currMax = do
  let thisIdx = lastIdx + 1
  idxAndMax <-
    ifM (xNoised %> currMax)
        (return (thisIdx, xNoised))-- reportNoisyMaxAux xs thisIdx thisIdx xNoised)
        (return (maxIdx, currMax)) -- reportNoisyMaxAux xs thisIdx maxIdx  currMax)
  reportNoisyMaxAuxOpt xs thisIdx (fst idxAndMax) (snd idxAndMax)

reportNoisyMaxOpt :: forall int m a.
                     (FuzziLang m a, FuzziType int, Numeric int)
                  => [Fuzzi a]
                  -> Mon m (Fuzzi int)
reportNoisyMaxOpt []     = error "reportNoisyMax received empty input"
reportNoisyMaxOpt (x:xs) = do
  xNoised <- lap x 1.0
  xsNoised <- mapM (`lap` 1.0) xs
  reportNoisyMaxAuxOpt xsNoised 0 0 xNoised

reportNoisyMax :: forall m a.
                  (FuzziLang m a)
               => [Fuzzi a]
               -> Mon m (Fuzzi Int)
reportNoisyMax []     = error "reportNoisyMax received empty input"
reportNoisyMax (x:xs) = do
  xNoised <- lap x 1.0
  xsNoised <- mapM (`lap` 1.0) xs
  reportNoisyMaxAux xsNoised 0 0 xNoised

reportNoisyMaxGap :: (FuzziLang m a)
                  => [Fuzzi a]
                  -> Mon m (Fuzzi Int, Fuzzi a)
reportNoisyMaxGap []  = error "reportNoisyMaxGap received empty input"
reportNoisyMaxGap [_] = error "reportNoisyMaxGap received only one input"
reportNoisyMaxGap (x:y:xs) = do
  xNoised <- lap x 1.0
  yNoised <- lap y 1.0
  xsNoised <- mapM (`lap` 1.0) xs
  --reportNoisyMaxGapAux xsNoised 0 0 xNoised xNoised
  ifM (xNoised %> yNoised)
      (reportNoisyMaxGapAux xsNoised 1 0 xNoised yNoised)
      (reportNoisyMaxGapAux xsNoised 1 1 yNoised xNoised)
  --ifM (x %> y)
  --  (reportNoisyMaxGapAux xs 1 0 x y)
  --  (reportNoisyMaxGapAux xs 1 1 y x)

reportNoisyMaxGapAux :: (FuzziLang m a)
                     => [Fuzzi a]             -- ^input data
                     -> Fuzzi Int             -- ^last iteration index
                     -> Fuzzi Int             -- ^current max index
                     -> Fuzzi a               -- ^current maximum
                     -> Fuzzi a               -- ^current runner-up
                     -> Mon m (Fuzzi Int, Fuzzi a)
reportNoisyMaxGapAux []           _       maxIdx currMax currRunnerUp =
  return (maxIdx, currMax - currRunnerUp)
reportNoisyMaxGapAux (xNoised:xs) lastIdx maxIdx currMax currRunnerUp = do
  let thisIdx = lastIdx + 1
  ifM (xNoised %> currMax)
      (reportNoisyMaxGapAux xs thisIdx thisIdx xNoised currMax)
      (ifM (xNoised %> currRunnerUp)
           (reportNoisyMaxGapAux xs thisIdx maxIdx currMax xNoised)
           (reportNoisyMaxGapAux xs thisIdx maxIdx currMax currRunnerUp)
      )

reportNoisyMaxGapOpt :: forall int m a.
                        (FuzziLang m a, FuzziType int, Numeric int)
                     => [Fuzzi a]
                     -> Mon m (Fuzzi int, Fuzzi a)
reportNoisyMaxGapOpt []  = error "reportNoisyMaxGap received empty input"
reportNoisyMaxGapOpt [_] = error "reportNoisyMaxGap received only one input"
reportNoisyMaxGapOpt (x:y:xs) = do
  xNoised <- lap x 1.0
  yNoised <- lap y 1.0
  xsNoised <- mapM (`lap` 1.0) xs
  (maxIdx, (currMax, currRunnerUp)) <-
    ifM (xNoised %> yNoised)
        (return (0, (xNoised, yNoised)))
        (return (1, (yNoised, xNoised)))
  reportNoisyMaxGapAuxOpt xsNoised 1 maxIdx currMax currRunnerUp

reportNoisyMaxGapAuxOpt :: forall int m a.
                           (FuzziLang m a, FuzziType int, Numeric int)
                        => [Fuzzi a]             -- ^input data
                        -> Fuzzi int             -- ^last iteration index
                        -> Fuzzi int             -- ^current max index
                        -> Fuzzi a               -- ^current maximum
                        -> Fuzzi a               -- ^current runner-up
                        -> Mon m (Fuzzi int, Fuzzi a)
reportNoisyMaxGapAuxOpt []           _       maxIdx currMax currRunnerUp =
  return (maxIdx, currMax - currRunnerUp)
reportNoisyMaxGapAuxOpt (xNoised:xs) lastIdx maxIdx currMax currRunnerUp = do
  let thisIdx = lastIdx + 1
  (maxIdx', (currMax', currRunnerUp')) <-
    ifM (xNoised %> currMax)
        (return (thisIdx, (xNoised, currMax)))
        (ifM (xNoised %> currRunnerUp)
             (return (maxIdx, (currMax, xNoised)))
             (return (maxIdx, (currMax, currRunnerUp)))
        )
  reportNoisyMaxGapAuxOpt xs thisIdx maxIdx' currMax' currRunnerUp'

reportNoisyMaxBuggy :: forall m a.
                       (FuzziLang m a)
                    => [Fuzzi a]
                    -> Mon m (Fuzzi Int)
reportNoisyMaxBuggy []     = error "reportNoisyMaxBuggy received empty input"
reportNoisyMaxBuggy (x:xs) = do
  _xNoised <- lap x 1.0
  xsNoised <- mapM (`lap` 1.0) xs
  reportNoisyMaxAux xsNoised 0 0 x

smartSumAux :: (FuzziLang m a)
            => [Fuzzi a] -- ^The inputs
            -> Fuzzi a   -- ^The next partial sum
            -> Fuzzi a   -- ^This partial sum
            -> Fuzzi Int -- ^Iteration index
            -> Fuzzi a   -- ^The un-noised raw sum
            -> Fuzzi [a] -- ^The accumulated list
            -> Mon m (Fuzzi [a])
smartSumAux []     _    _ _ _   results = return results
smartSumAux (x:xs) next n i sum results = do
  let sum' = sum + x
  if_ (((i + 1) `imod` 2) %== 0)
      (do n' <- lap (n + sum') 1.0
          smartSumAux xs n'    n' (i+1) 0    (results `snoc` n'))
      (do next' <- lap (next + x) 1.0
          smartSumAux xs next' n  (i+1) sum' (results `snoc` next'))

smartSumAuxBuggy :: (FuzziLang m a)
                 => [Fuzzi a] -- ^The inputs
                 -> Fuzzi a   -- ^The next partial sum
                 -> Fuzzi a   -- ^This partial sum
                 -> Fuzzi Int -- ^Iteration index
                 -> Fuzzi a   -- ^The un-noised raw sum
                 -> Fuzzi [a] -- ^The accumulated list
                 -> Mon m (Fuzzi [a])
smartSumAuxBuggy []     _    _ _ _   results = return results
smartSumAuxBuggy (x:xs) next n i sum results = do
  let sum' = sum + x
  if_ (((i + 1) `imod` 2) %== 0)
      (do n' <- lapNoTolerance (n + sum') 1.0
          smartSumAuxBuggy xs n'    n' (i+1) sum' (results `snoc` n'))    -- here's the bug
      (do next' <- lapNoTolerance (next + x) 1.0
          smartSumAuxBuggy xs next' n  (i+1) sum' (results `snoc` next'))
  where lapNoTolerance = lap' 0

prefixSum :: forall m a.
             (FuzziLang m a)
          => [Fuzzi a]
          -> Mon m (Fuzzi [a])
prefixSum xs = do
  xsNoised <- mapM (`lap` 1.0) xs
  return (prefixSumAux (reverse xsNoised) nil)

prefixSumAux :: (FuzziType a, Numeric a)
             => [Fuzzi a]
             -> Fuzzi [a]
             -> Fuzzi [a]
prefixSumAux []           acc = acc
prefixSumAux input@(_x:xs) acc = prefixSumAux xs (sum input `cons` acc)

smartSum :: forall m a.
            (FuzziLang m a)
         => [Fuzzi a]
         -> Mon m (Fuzzi [a])
-- smartSum :: forall m a listA. _ => [Fuzzi a] -> Mon m (Fuzzi listA)
smartSum xs = smartSumAux xs 0 0 0 0 nil

smartSumBuggy :: forall m a.
                 (FuzziLang m a)
              => [Fuzzi a]
              -> Mon m (Fuzzi [a])
-- smartSumBuggy :: forall m a listA. _ => [Fuzzi a] -> Mon m (Fuzzi listA)
smartSumBuggy xs = smartSumAuxBuggy xs 0 0 0 0 nil

sparseVector :: (FuzziLang m a)
             => [Fuzzi a] -- ^ input data
             -> Int       -- ^ maximum number of above thresholds
             -> Fuzzi a   -- ^ threshold
             -> Mon m (Fuzzi [Bool])
sparseVector xs n threshold = do
  noisedThreshold <- lap threshold 2.0
  noisedXs <- mapM (`lap` (4.0 * fromIntegral n)) xs
  sparseVectorAux noisedXs n noisedThreshold nil

sparseVectorAux :: (FuzziLang m a)
                => [Fuzzi a]
                -> Int
                -> Fuzzi a
                -> Fuzzi [Bool]
                -> Mon m (Fuzzi [Bool])
sparseVectorAux []     _n _threshold acc = return acc
sparseVectorAux (x:xs) n threshold acc
  | n <= 0    = return acc
  | otherwise =
      ifM (x %> threshold)
          (sparseVectorAux xs (n-1) threshold (acc `snoc` lit True))
          (sparseVectorAux xs n     threshold (acc `snoc` lit False))

sparseVectorGap :: (FuzziLang m a)
                => [Fuzzi a]
                -> Int
                -> Fuzzi a
                -> Mon m (Fuzzi [Maybe a])
sparseVectorGap xs n threshold = do
  noisedThreshold <- lap threshold 2.0
  noisedXs <- mapM (`lap` (4.0 * fromIntegral n)) xs
  sparseVectorGapAux noisedXs n noisedThreshold nil

sparseVectorGapAux :: (FuzziLang m a)
                   => [Fuzzi a]
                   -> Int
                   -> Fuzzi a
                   -> Fuzzi [Maybe a]
                   -> Mon m (Fuzzi [Maybe a])
sparseVectorGapAux []     _n _threshold acc = return acc
sparseVectorGapAux (x:xs)  n  threshold acc
  | n <= 0 = return acc
  | otherwise =
    ifM (x %> threshold)
        (sparseVectorGapAux xs (n-1) threshold (acc `snoc` just (x - threshold)))
        (sparseVectorGapAux xs n     threshold (acc `snoc` nothing))

sparseVectorBuggy :: forall m a.
                     (FuzziLang m a)
                  => [Fuzzi a] -- ^ input data
                  -> Int       -- ^ maximum number of above thresholds
                  -> Fuzzi a   -- ^ threshold
                  -> Mon m (Fuzzi [a])
sparseVectorBuggy xs n threshold = do
  noisedThreshold <- lap threshold 2.0
  noisedXs <- mapM (`lap` (4.0 * fromIntegral n)) xs
  sparseVectorBuggyAux noisedXs n noisedThreshold (nil @a)

sparseVectorBuggyAux :: (FuzziLang m a)
                     => [Fuzzi a]
                     -> Int
                     -> Fuzzi a
                     -> Fuzzi [a]
                     -> Mon m (Fuzzi [a])
sparseVectorBuggyAux []     _n _threshold acc = return acc
sparseVectorBuggyAux (x:xs) n  threshold  acc
  | n <= 0    = return acc
  | otherwise =
      ifM (x %> threshold)
          (sparseVectorBuggyAux xs (n-1) threshold (acc `snoc` x))
          (sparseVectorBuggyAux xs n     threshold (acc `snoc` 0))

k_PT_LAMBDA :: (Fractional a) => a
k_PT_LAMBDA = 1.0

k_PT_GAMMA :: (Fractional a) => a
k_PT_GAMMA = 1.0

k_PT_DELTA :: (Fractional a) => a
k_PT_DELTA = k_PT_LAMBDA * k_PT_GAMMA

k_PT_EPSILON :: (Floating a) => a
k_PT_EPSILON = (2 * exp k_PT_GAMMA - 1) / (exp k_PT_GAMMA - 1) / k_PT_LAMBDA

k_PT_THRESHOLD :: (Fractional a) => a
k_PT_THRESHOLD = 2

k_PT_MAX_LEAF_NODES :: (Num a) => a
k_PT_MAX_LEAF_NODES = 5

privTree :: (FuzziLang m a) => [Double] -> Mon m (Fuzzi (PrivTree1D Bool))
privTree xs =
  privTreeAux xs [rootNode] (S.singleton rootNode) (lit emptyTree)

privTreeAux :: forall m a.
               (FuzziLang m a)
            => [Double]                     -- ^input points on the unit interval
            -> [PrivTreeNode1D]             -- ^queue of unvisited nodes
            -> S.Set PrivTreeNode1D         -- ^current set of leaf nodes
            -> Fuzzi (PrivTree1D Bool)         -- ^current tree
            -> Mon m (Fuzzi (PrivTree1D Bool))
privTreeAux points queue leafNodes tree
  | length leafNodes > k_PT_MAX_LEAF_NODES
  = abort "unreachable code: there are too many leaf nodes"
  | otherwise
  = case queue of
      [] -> return tree
      (thisNode:more) -> do
        let biasedCount = countPoints points thisNode - depth thisNode * k_PT_DELTA
        biasedCount' <-
          ifM (biasedCount %> (k_PT_THRESHOLD - k_PT_DELTA))
              (return biasedCount)
              (return $ k_PT_THRESHOLD - k_PT_DELTA)
        noisedBiasedCount1 <- lap biasedCount' k_PT_LAMBDA
        let updatedTree = updatePT (lit thisNode) true tree
        ifM (noisedBiasedCount1 %> k_PT_THRESHOLD)
            (do let (left, right) = split thisNode
                let leafNodes' =
                      S.insert right (S.insert left (S.delete thisNode leafNodes))
                if length leafNodes' <= k_PT_MAX_LEAF_NODES
                then privTreeAux points (more++[left,right]) leafNodes' updatedTree
                else abort "unreachable code: there are too many leaf nodes"
            )
            (privTreeAux
               points
               more
               leafNodes
               updatedTree)

privTreeBuggy :: (FuzziLang m a) => [Double] -> Mon m (Fuzzi (PrivTree1D a))
privTreeBuggy xs =
  privTreeBuggyAux xs [rootNode] (S.singleton rootNode) (lit emptyTree)

privTreeBuggyAux :: forall m a.
                    (FuzziLang m a)
                 => [Double]                     -- ^input points on the unit interval
                 -> [PrivTreeNode1D]             -- ^queue of unvisited nodes
                 -> S.Set PrivTreeNode1D         -- ^current set of leaf nodes
                 -> Fuzzi (PrivTree1D a)         -- ^current tree
                 -> Mon m (Fuzzi (PrivTree1D a))
privTreeBuggyAux points queue leafNodes tree
  | length leafNodes > k_PT_MAX_LEAF_NODES
  = abort "unreachable code: there are too many leaf nodes"
  | otherwise
  = case queue of
      [] -> return tree
      (thisNode:more) -> do
        let naiveCount = countPoints points thisNode
        noisedNaiveCount <- lap naiveCount k_PT_LAMBDA
        let updatedTree = updatePT (lit thisNode) noisedNaiveCount tree
        ifM (noisedNaiveCount %> k_PT_THRESHOLD)
            (do let (left, right) = split thisNode
                let leafNodes' =
                      S.insert right (S.insert left (S.delete thisNode leafNodes))
                if length leafNodes' <= length points
                then privTreeBuggyAux points (more++[left,right]) leafNodes' updatedTree
                else abort "unreachable code: there are too many leaf nodes"
            )
            (privTreeBuggyAux
               points
               more
               leafNodes
               updatedTree)

privTreeBuggy2 :: (FuzziLang m a) => [Double] -> Mon m (Fuzzi (PrivTree1D a))
privTreeBuggy2 xs =
  privTreeBuggy2Aux xs [rootNode] (S.singleton rootNode) (lit emptyTree)

privTreeBuggy2Aux :: forall m a.
               (FuzziLang m a)
            => [Double]                     -- ^input points on the unit interval
            -> [PrivTreeNode1D]             -- ^queue of unvisited nodes
            -> S.Set PrivTreeNode1D         -- ^current set of leaf nodes
            -> Fuzzi (PrivTree1D a)         -- ^current tree
            -> Mon m (Fuzzi (PrivTree1D a))
privTreeBuggy2Aux points queue leafNodes tree
  | length leafNodes > k_PT_MAX_LEAF_NODES
  = abort "unreachable code: there are too many leaf nodes"
  | otherwise
  = case queue of
      [] -> return tree
      (thisNode:more) -> do
        let biasedCount = countPoints points thisNode - depth thisNode * k_PT_DELTA
        biasedCount' <-
          ifM (biasedCount %> (k_PT_THRESHOLD - k_PT_DELTA))
              (return biasedCount)
              (return $ k_PT_THRESHOLD - k_PT_DELTA)
        noisedBiasedCount1 <- lap biasedCount' k_PT_LAMBDA
        let updatedTree = updatePT (lit thisNode) noisedBiasedCount1 tree
        ifM (noisedBiasedCount1 %> k_PT_THRESHOLD)
            (do let (left, right) = split thisNode
                let leafNodes' =
                      S.insert right (S.insert left (S.delete thisNode leafNodes))
                if length leafNodes' <= k_PT_MAX_LEAF_NODES
                then privTreeBuggy2Aux points (more++[left,right]) leafNodes' updatedTree
                else abort "unreachable code: there are too many leaf nodes"
            )
            (privTreeBuggy2Aux
               points
               more
               leafNodes
               updatedTree)

simpleCount :: forall m a.
               (FuzziLang m a)
            => [Int]
            -> Int
            -> Mon m (Fuzzi a)
simpleCount xs threshold = do
  let c = length (filter (>= threshold) xs)
  lap (fromIntegral c) 1.0

simpleMean :: forall m a.
              (FuzziLang m a, Ord a)
           => [Fuzzi a] -- input data
           -> a         -- clip range
           -> Mon m (Fuzzi a, Fuzzi a)
simpleMean xs clipBound
  | clipBound < 0 = error "simpleMean: received clipBound < 0"
  | otherwise = do
      s <- clippedSum xs 0
      noisedS <- lap s 1.0
      noisedC <- lap count 1.0
      return (noisedS, noisedC)
  where clippedSum []     acc = return acc
        clippedSum (x:xs) acc =
          ifM (x %>= lit clipBound)
              (clippedSum xs (acc + lit clipBound))
              (ifM (x %< lit (-clipBound))
                   (clippedSum xs (acc - lit clipBound))
                   (clippedSum xs (acc + x))
              )

        count = fromIntegral_ (lit (length xs))

unboundedMean :: forall m a.
                 (FuzziLang m a)
              => [Fuzzi a]
              -> Mon m (Fuzzi a, Fuzzi a)
unboundedMean xs = do
  noisedS <- lap (sum xs) 1.0
  noisedC <- lap count 1.0
  return (noisedS, noisedC)
  where count = fromIntegral_ (lit (length xs))
