module MSSSpec where

import Common.Spec
import Control.Monad.Except
import GHC.Stack
import Grisette

mssAlgo :: (Num a, Ord a) => [a] -> a
mssAlgo = go 0 0
  where
    go suffix best [] = max suffix best
    go suffix best (x : xs) = go (max 0 suffix + x) (max suffix best) xs

isConsecutive0 :: [Int] -> Bool
isConsecutive0 [] = True
isConsecutive0 (0 : xs) = isConsecutive0 xs
isConsecutive0 (1 : xs) = isConsecutive1 xs
isConsecutive0 (_ : _) = undefined

isConsecutive1 :: [Int] -> Bool
isConsecutive1 [] = True
isConsecutive1 (1 : xs) = isConsecutive1 xs
isConsecutive1 (0 : xs) = all (== 0) xs
isConsecutive1 (_ : _) = undefined

allBitStrings :: Int -> [[Int]]
allBitStrings i = filter isConsecutive0 $ replicateM i [0 :: Int, 1]

apply :: (HasCallStack, Show a2, Num a2) => [[a2]] -> [Int] -> a2
apply [[]] [] = 0
apply [_ : xs] (0 : ys) = apply [xs] ys
apply [x : xs] (1 : ys) = x + apply [xs] ys
apply _ _ = undefined

mssSpec :: forall a e. (HasCallStack, Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
mssSpec = spec apply allBitStrings

mssSpecV :: forall a e. (HasCallStack, Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
mssSpecV = specV apply allBitStrings
