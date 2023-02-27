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

mis :: (Num a) => ConProgram a
mis =
  ConProgram
    -- pick no_pick
    [0, 0]
    [ ConBinary "+" (ConArg 0) (ConArg 2),
      ConBinary "max" (ConArg 1) (ConArg 2)
    ]
    (ConBinary "max" (ConArg 0) (ConArg 1))
    1

misSketchComb :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s) => proxy c -> Program s
misSketchComb _ =
  genSymSimple
    (CombProgramSpec @c @s [0] (CombASTSpec0 1 1 ["zero", "id"] ["+", "max"]) (CombASTSpec0 0 1 [] ["max"]) 2 1)
    "mis"

misSketchExt :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s) => proxy c -> Program s
misSketchExt _ =
  genSymSimple
    (ExtProgramSpec @c @s [0] (CombASTSpec0 1 1 ["zero", "id"] ["+"]) "max" 1 2 2 1)
    "misopt"

misAlgo :: forall a. (Num a, Ord a) => [a] -> a
misAlgo = go 0 0
  where
    go pick no_pick [] = max pick no_pick
    go pick no_pick (x : xs) = go (no_pick + x) (max pick no_pick) xs

isNotConsecutive :: [Int] -> Bool
isNotConsecutive [] = True
isNotConsecutive [_] = True
isNotConsecutive (1 : 1 : _) = False
isNotConsecutive (_ : x : xs) = isNotConsecutive (x : xs)

allBitStrings :: Int -> [[Int]]
allBitStrings i = filter isNotConsecutive $ replicateM i [0 :: Int, 1]

apply :: (Num a2) => [[a2]] -> [Int] -> a2
apply [] [] = 0
apply (_ : xs) (0 : ys) = apply xs ys
apply ([x] : xs) (1 : ys) = x + apply xs ys
apply _ _ = undefined

safeApply :: (Num a, Mergeable a, SafeLinearArith e a) => [[a]] -> [Int] -> ExceptT VerificationConditions UnionM a
safeApply [] [] = mrgReturn 0
safeApply (_ : xs) (0 : ys) = safeApply xs ys
safeApply ([x] : xs) (1 : ys) = do
  a <- safeApply xs ys
  safeAdd' (const AssumptionViolation) x a
safeApply _ _ = undefined

misSpec :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
misSpec = spec apply allBitStrings

safeMisSpec :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
safeMisSpec = safeSpec safeApply allBitStrings

misSpecV :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
misSpecV = specV apply allBitStrings

safeMisSpecV :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
safeMisSpecV = safeSpecV safeApply allBitStrings

main :: IO ()
main = do
  let config = precise z3

  misIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "misextV" $ synth1V config availableUnary availableBinary () (const $ con True) (misSpecV @SymInteger) (misSketchExt (Proxy @Integer))
  print misIntSynthedExtV

  misIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "miscombV" $ synth1V config availableUnary availableBinary () (const $ con True) (misSpecV @SymInteger) (misSketchComb (Proxy @Integer))
  print misIntSynthedCombV
