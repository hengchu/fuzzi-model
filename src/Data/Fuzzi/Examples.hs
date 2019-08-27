module Data.Fuzzi.Examples where

import Data.Fuzzi.Interface

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

smartSumAux :: ( FuzziLang m a
               , ListLike listA
               , Elem listA ~ a
               , FuzziType listA
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
          smartSumAux xs n' n' (i+1) sum' (results `snoc` n'))
      (do next' <- lap (next + x) 1.0
          smartSumAux xs next' n (i+1) sum' (results `snoc` next'))

smartSum :: forall m a listA.
            ( FuzziLang m a
            , ListLike listA
            , Elem listA ~ a
            , FuzziType listA
            , ConcreteBoolean (TestResult listA))
         => [Fuzzi a]
         -> Mon m (Fuzzi listA)
-- smartSum :: forall m a listA. _ => [Fuzzi a] -> Mon m (Fuzzi listA)
smartSum xs = smartSumAux xs 0 0 0 0 nil
