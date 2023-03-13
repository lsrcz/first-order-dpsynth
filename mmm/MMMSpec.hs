module MMMSpec where

import Grisette
import Control.Monad.Except
import Spec

mmmAlgo :: forall a. (Num a, Ord a) => [a] -> a
mmmAlgo = go 0 0 0
  where
    go ign pos neg [] = max (max ign pos) neg
    go ign pos neg (x : xs) = go (max pos neg) (max (ign + x) (neg + x)) (max (ign - x) (pos - x)) xs

isNotConsecutive :: [Int] -> Bool
isNotConsecutive [] = True
isNotConsecutive [_] = True
isNotConsecutive (1 : 1 : _) = False
isNotConsecutive (0 : 0 : _) = False
isNotConsecutive (-1 : -1 : _) = False
isNotConsecutive (_ : x : xs) = isNotConsecutive (x : xs)

allBitStrings :: Int -> [[Int]]
allBitStrings i = filter isNotConsecutive $ replicateM i [0, 1, -1]

apply :: (Show a2, Num a2) => [[a2]] -> [Int] -> a2
apply [[]] [] = 0
apply [_ : xs] (0 : ys) = apply [xs] ys
apply [x : xs] (1 : ys) = x + apply [xs] ys
apply [x : xs] (-1 : ys) = -x + apply [xs] ys
apply _ _ = undefined

safeApply :: (SimpleMergeable a, Num a, SafeLinearArith e a) => [[a]] -> [Int] -> ExceptT VerificationConditions UnionM a
safeApply [[]] [] = mrgReturn 0
safeApply [_ : xs] (0 : ys) = safeApply [xs] ys
safeApply [x : xs] (1 : ys) = do
  ax <- safeApply [xs] ys
  safeAdd' (const AssumptionViolation) x ax
safeApply [x : xs] (-1 : ys) = do
  ax <- safeApply [xs] ys
  safeMinus' (const AssumptionViolation) ax x
safeApply _ _ = undefined

mmmSpecV :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
mmmSpecV = specV apply allBitStrings

safeMmmSpecV :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
safeMmmSpecV = safeSpecV safeApply allBitStrings

mmmSpec :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
mmmSpec = spec apply allBitStrings

safeMmmSpec :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
safeMmmSpec = safeSpec safeApply allBitStrings