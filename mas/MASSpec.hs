module MASSpec where

import Common.Spec
import Control.Monad.Except
import Grisette

masAlgo :: (Num a, Ord a) => [a] -> a
masAlgo = go 0 0 0
  where
    go suffix_pos suffix_neg best [] = max (max suffix_pos suffix_neg) best
    go suffix_pos suffix_neg best (x : xs) =
      go (max 0 suffix_neg + x) (max 0 suffix_pos - x) (max (max suffix_pos suffix_neg) best) xs

isConsecutive0begin :: [Int] -> Bool
isConsecutive0begin [] = True
isConsecutive0begin (0 : xs) = isConsecutive0begin xs
isConsecutive0begin (1 : xs) = isAlternativem1 xs
isConsecutive0begin (-1 : xs) = isAlternative1 xs
isConsecutive0begin (_ : _) = undefined

isAlternative1 :: [Int] -> Bool
isAlternative1 [] = True
isAlternative1 (0 : xs) = isConsecutive0 xs
isAlternative1 (1 : xs) = isAlternativem1 xs
isAlternative1 (-1 : _) = False
isAlternative1 (_ : _) = undefined

isAlternativem1 :: [Int] -> Bool
isAlternativem1 [] = True
isAlternativem1 (0 : xs) = isConsecutive0 xs
isAlternativem1 (-1 : xs) = isAlternative1 xs
isAlternativem1 (1 : _) = False
isAlternativem1 (_ : _) = undefined

isConsecutive0 :: [Int] -> Bool
isConsecutive0 [] = True
isConsecutive0 (0 : xs) = isConsecutive0 xs
isConsecutive0 (-1 : _) = False
isConsecutive0 (1 : _) = False
isConsecutive0 (_ : _) = undefined

allBitStrings :: Int -> [[Int]]
allBitStrings i = filter isConsecutive0begin $ replicateM i [0 :: Int, 1, -1]

apply :: (Num a2) => [[a2]] -> [Int] -> a2
apply [[]] [] = 0
apply [_ : xs] (0 : ys) = apply [xs] ys
apply [x : xs] (1 : ys) = x + apply [xs] ys
apply [x : xs] (-1 : ys) = apply [xs] ys - x
apply _ _ = undefined

masSpec :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
masSpec = spec apply allBitStrings

masSpecV :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
masSpecV = specV apply allBitStrings
