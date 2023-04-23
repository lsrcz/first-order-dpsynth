module SecondMinSpec where

import Control.Monad.Except
import Data.Foldable
import Grisette
import GHC.Stack
import Data.List

secondMinInf :: (HasCallStack, Ord a) => a -> [a] -> a
secondMinInf inf [] = inf
secondMinInf inf [_] = inf
secondMinInf _ l = (!!1) . sort $ l

secondMin :: (HasCallStack, Ord a) => [a] -> a
secondMin = (!!1) . sort

minSpecV :: [[SymInteger]] -> SymInteger -> ExceptT VerificationConditions UnionM SymBool
minSpecV inputs v = do
  symAssume $ con $ length t >= 2
  mrgTraverse_ (\x -> symAssume $ x <=~ 0 &&~ x >=~ -16) t
  mrgReturn $
    (numl <~ 2) &&~ (numle >=~ 2) &&~ (numl <~ numle)
  where
    t = head inputs
    tl = map (\x -> mrgIte (x <~ v :: SymBool) (1 :: SymInteger) 0) t
    tle = map (\x -> mrgIte (x <=~ v :: SymBool) (1 :: SymInteger) 0) t
    numl = foldl' (+) 0 tl
    numle = foldl' (+) 0 tle

minSpec :: (Num a, SOrd a, Mergeable a) => [[a]] -> ExceptT VerificationConditions UnionM a
minSpec inputs = do
  symAssume $ con $ length t >= 2
  mrgTraverse_ (\x -> symAssume $ x <=~ 0 &&~ x >=~ -16) t
  go t
  where
    t = head inputs
    go [] = throwError AssumptionViolation
    go (x:xs) = mrgIf (f x) (mrgReturn x) (go xs)
    f v = (numl <~ 2) &&~ (numle >=~ 2) &&~ (numl <~ numle)
      where
        tl = map (\x -> mrgIte (x <~ v :: SymBool) (1 :: SymInteger) 0) t
        tle = map (\x -> mrgIte (x <=~ v :: SymBool) (1 :: SymInteger) 0) t
        numl = foldl' (+) 0 tl
        numle = foldl' (+) 0 tle
