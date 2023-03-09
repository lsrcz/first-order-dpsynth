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
import Test.QuickCheck
import Interpreter

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

isConsecutive0begin :: [Int] -> Bool
isConsecutive0begin [] = True
isConsecutive0begin (0 : xs) = isConsecutive0begin xs
isConsecutive0begin (1 : xs) = isAlternativem1 xs
isConsecutive0begin (-1 : xs) = isAlternative1 xs
isConsecutive0begin (_ : _) = undefined

isAlternative1 :: [Int] -> Bool
isAlternative1 [] = True
isAlternative1 (0:xs) = isConsecutive0 xs
isAlternative1 (1:xs) = isAlternativem1 xs
isAlternative1 (-1:_) = False
isAlternative1 (_ : _) = undefined

isAlternativem1 :: [Int] -> Bool
isAlternativem1 [] = True
isAlternativem1 (0:xs) = isConsecutive0 xs
isAlternativem1 (-1:xs) = isAlternative1 xs
isAlternativem1 (1:_) = False
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

cap :: (SOrd a, Num a) => [[a]] -> SymBool
cap = foldl (\acc y -> acc &&~ y >=~ -3 &&~ y <=~ 3) (con True) . join

main :: IO ()
main = do
  let config = precise z3

  Just masIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "masextV" $ synth1V config availableUnary availableBinary () (const $ con True) (masSpecV @SymInteger) (masSketchExt (Proxy @Integer))
  print masIntSynthedExtV

  quickCheck (\(l :: [Integer]) -> interpretSketch availableUnary availableBinary (toSym masIntSynthedExtV) [toSym l] == mrgReturn (toSym $ masAlgo l :: SymInteger))

  Just masIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "mascombV" $ synth1V config availableUnary availableBinary () (const $ con True) (masSpecV @SymInteger) (masSketchComb (Proxy @Integer))
  print masIntSynthedCombV
