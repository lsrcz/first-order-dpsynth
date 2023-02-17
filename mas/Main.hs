module Main where

import Control.Monad.Except
import Core
import Data.Proxy
import Gen
import Grisette
import Ops
import Query
import Spec
import Timing

mas :: Num a => ConProgram a
mas =
  ConProgram
    -- suffix_pos suffix_neg best
    [0, 0, 0]
    [ ConBinary "max" (ConArg 0) (ConBinary "+" (ConArg 0) (ConArg 2)),
      ConBinary "max" (ConUnary "-" (ConArg 0)) (ConBinary "+" (ConArg 1) (ConUnary "-" (ConArg 0))),
      ConBinary "max" (ConBinary "max" (ConArg 1) (ConArg 2)) (ConArg 3)
    ]
    (ConBinary "max" (ConBinary "max" (ConArg 0) (ConArg 1)) (ConArg 2))
    1

masSynthed :: Num a => ConProgram a
masSynthed =
  ConProgram
    -- suffix_pos suffix_neg best
    [0, 0, 0]
    [ ConBinary "max" (ConUnary "zero" (ConArg 0)) (ConBinary "-" (ConArg 3) (ConArg 0)),
      ConBinary "max" (ConArg 2) (ConBinary "max" (ConBinary "+" (ConArg 1) (ConArg 0)) (ConBinary "-" (ConArg 3) (ConArg 0))),
      ConBinary "max" (ConUnary "zero" (ConArg 0)) (ConBinary "+" (ConArg 1) (ConArg 0))
    ]
    (ConBinary "max" (ConBinary "max" (ConArg 0) (ConArg 1)) (ConArg 2))
    1

masAlgo :: (Num a, Ord a) => [a] -> a
masAlgo = go 0 0 0
  where
    go suffix_pos suffix_neg best [] = max (max suffix_pos suffix_neg) best
    go suffix_pos suffix_neg best (x : xs) =
      go (max 0 suffix_neg + x) (max 0 suffix_pos - x) (max (max suffix_pos suffix_neg) best) xs

masSketchComb :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s) => proxy c -> Program s
masSketchComb _ =
  genSymSimple
    (CombProgramSpec @c @s [0] (CombASTSpec0 1 3 ["-", "id", "zero"] ["+", "max"]) (CombASTSpec0 0 2 [] ["max"]) 3 1)
    "mas"

masSketchExt :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s) => proxy c -> Program s
masSketchExt _ =
  genSymSimple
    (ExtProgramSpec @c @s [0] (CombASTSpec0 1 1 ["-", "id", "zero"] ["+"]) "max" 2 3 3 1)
    "mas"

isConsecutive0 :: [Int] -> Bool
isConsecutive0 [] = True
isConsecutive0 (0 : xs) = isConsecutive0 xs
isConsecutive0 (1 : xs) = isConsecutive1 xs
isConsecutive0 (-1 : xs) = isConsecutivem1 xs
isConsecutive0 (_ : _) = undefined

isConsecutive1 :: [Int] -> Bool
isConsecutive1 [] = True
isConsecutive1 (1 : _) = False
isConsecutive1 (-1 : xs) = isConsecutivem1 xs
isConsecutive1 (0 : xs) = all (== 0) xs
isConsecutive1 (_ : _) = undefined

isConsecutivem1 :: [Int] -> Bool
isConsecutivem1 [] = True
isConsecutivem1 (-1 : _) = False
isConsecutivem1 (1 : xs) = isConsecutive1 xs
isConsecutivem1 (0 : xs) = all (== 0) xs
isConsecutivem1 (_ : _) = undefined

allBitStrings :: Int -> [[Int]]
allBitStrings i = filter isConsecutive0 $ replicateM i [0 :: Int, 1, -1]

apply :: (Num a2) => [[a2]] -> [Int] -> a2
apply [] [] = 0
apply (_ : xs) (0 : ys) = apply xs ys
apply ([x] : xs) (1 : ys) = x + apply xs ys
apply ([x] : xs) (-1 : ys) = apply xs ys - x
apply _ _ = undefined

masSpec :: forall a. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith a) => [[a]] -> ExceptT VerificationConditions UnionM a
masSpec = spec apply allBitStrings

masSpecV :: forall a. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
masSpecV = specV apply allBitStrings

cap :: (SOrd a, Num a) => [[a]] -> SymBool
cap = foldl (\acc y -> acc &&~ y >=~ -3 &&~ y <=~ 3) (con True) . join

main :: IO ()
main = do
  let config = precise z3

  masIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "masextV" $ synth1V config availableUnary availableBinary () (const $ con True) (masSpecV @SymInteger) (masSketchExt (Proxy @Integer))
  print masIntSynthedExtV

  masIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "mascombV" $ synth1V config availableUnary availableBinary () (const $ con True) (masSpecV @SymInteger) (masSketchComb (Proxy @Integer))
  print masIntSynthedCombV
