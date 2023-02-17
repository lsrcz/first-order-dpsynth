module Main where

import Control.Monad
import Control.Monad.Except
import Core
import Data.Proxy
import Gen
import Grisette
import Ops
import Query
import Spec
import Timing

mmm :: Num a => ConProgram a
mmm =
  ConProgram
    -- ign pos neg
    [0, 0, 0]
    [ ConBinary "max" (ConArg 2) (ConArg 3),
      ConBinary
        "max"
        (ConBinary "+" (ConArg 1) (ConArg 0))
        (ConBinary "+" (ConArg 3) (ConArg 0)),
      ConBinary
        "max"
        (ConBinary "-" (ConArg 1) (ConArg 0))
        (ConBinary "-" (ConArg 2) (ConArg 0))
    ]
    (ConBinary "max" (ConBinary "max" (ConArg 0) (ConArg 1)) (ConArg 2))
    1

mmmSketchComb :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s) => proxy c -> Program s
mmmSketchComb _ =
  genSymSimple
    (CombProgramSpec @c @s [0] (CombASTSpec0 1 3 ["zero", "id", "-"] ["+", "max"]) (CombASTSpec0 0 1 [] ["max"]) 3 1)
    "mmm"

mmmSketchExt :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s) => proxy c -> Program s
mmmSketchExt _ =
  genSymSimple
    (ExtProgramSpec @c @s [0] (CombASTSpec0 1 1 ["zero", "id", "-"] ["+"]) "max" 2 2 3 1)
    "misopt"

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

apply :: (Num a2) => [[a2]] -> [Int] -> a2
apply [] [] = 0
apply (_ : xs) (0 : ys) = apply xs ys
apply ([x] : xs) (1 : ys) = x + apply xs ys
apply ([x] : xs) (-1 : ys) = -x + apply xs ys
apply _ _ = undefined

safeApply :: (SimpleMergeable a, Num a, SafeLinearArith a) => [[a]] -> [Int] -> ExceptT VerificationConditions UnionM a
safeApply [] [] = mrgReturn 0
safeApply (_ : xs) (0 : ys) = safeApply xs ys
safeApply ([x] : xs) (1 : ys) = do
  a <- safeApply xs ys
  safeAdd AssumptionViolation x a
safeApply ([x] : xs) (-1 : ys) = do
  a <- safeApply xs ys
  safeMinus AssumptionViolation a x
safeApply _ _ = undefined

mmmSpecV :: forall a. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
mmmSpecV = specV apply allBitStrings

safeMmmSpecV :: forall a. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
safeMmmSpecV = safeSpecV safeApply allBitStrings

mmmSpec :: forall a. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith a) => [[a]] -> ExceptT VerificationConditions UnionM a
mmmSpec = spec apply allBitStrings

safeMmmSpec :: forall a. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith a) => [[a]] -> ExceptT VerificationConditions UnionM a
safeMmmSpec = safeSpec safeApply allBitStrings

cap :: (SOrd a, Num a) => [[a]] -> SymBool
cap = foldl (\acc y -> acc &&~ y >=~ -16 &&~ y <=~ 16) (con True) . join

main :: IO ()
main = do
  let config = precise z3

  mmmIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "mmmextV" $ synth1V config availableUnary availableBinary () (const $ con True) (mmmSpecV @SymInteger) (mmmSketchExt (Proxy @Integer))
  print mmmIntSynthedExtV

  mmmIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "mmmcombV" $ synth1V config availableUnary availableBinary () (const $ con True) (mmmSpecV @SymInteger) (mmmSketchComb (Proxy @Integer))
  print mmmIntSynthedCombV
