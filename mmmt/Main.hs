module Main where

import Control.Monad
import Control.Monad.Except
import Core
import Gen
import Grisette
import Query
import Timing
import TType

mmm :: ConProgram UT
mmm =
  ConProgram
    -- ign pos neg
    (mrgI <$> [0, 0, 0])
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

mmmSketchComb :: Program UT
mmmSketchComb =
  genSymSimple
    (CombProgramSpec @CT @UT [CI 0] (CombASTSpec0 1 3 ["zero", "id", "-"] ["+", "max"]) (CombASTSpec0 0 1 [] ["max"]) 3 1)
    "mmm"

mmmSketchExt :: Program UT
mmmSketchExt =
  genSymSimple
    (ExtProgramSpec @CT @UT [CI 0] (CombASTSpec0 1 1 ["zero", "id", "-"] ["+"]) "max" 2 2 3 1)
    "misopt"

isNotConsecutive :: [Int] -> Bool
isNotConsecutive [] = True
isNotConsecutive [_] = True
isNotConsecutive (1 : 1 : _) = False
isNotConsecutive (0 : 0 : _) = False
isNotConsecutive (-1 : -1 : _) = False
isNotConsecutive (_ : x : xs) = isNotConsecutive (x : xs)

allBitStrings :: Int -> [[Int]]
allBitStrings i = filter isNotConsecutive $ replicateM i [0, 1, -1]

apply :: [[SymInteger]] -> [Int] -> SymInteger
apply [] [] = 0
apply (_ : xs) (0 : ys) = apply xs ys
apply ([x] : xs) (1 : ys) = x + apply xs ys
apply ([x] : xs) (-1 : ys) = -x + apply xs ys
apply _ _ = undefined

extractInteger :: T -> ExceptT VerificationConditions UnionM SymInteger
extractInteger (B _) = mrgThrowError AssumptionViolation
extractInteger (I i) = mrgReturn i

safeApplyUT :: [[UnionM T]] -> [Int] -> ExceptT VerificationConditions UnionM (UnionM T)
safeApplyUT l i = do
  l' <- l1
  mrgReturn $ mrgReturn $ I (apply l' i)
  where
    l1 = (mrgTraverse . mrgTraverse) (extractInteger#~) l

safeMmmSpecV :: [[UT]] -> UT -> ExceptT VerificationConditions UnionM SymBool
safeMmmSpecV = safeSpecVUT safeApplyUT allBitStrings

main :: IO ()
main = do
  let config = precise z3
  return ()

  mmmIntSynthedExtV :: Maybe (ConProgram CT) <-
    timeItAll "mmmextV" $ synth1V config availableUnaryT availableBinaryT IntVal (const $ con True) (safeMmmSpecV) mmmSketchExt
  print mmmIntSynthedExtV

  mmmIntSynthedCombV :: Maybe (ConProgram CT) <-
    timeItAll "mmmcombV" $ synth1V config availableUnaryT availableBinaryT IntVal (const $ con True) safeMmmSpecV mmmSketchComb
  print mmmIntSynthedCombV
