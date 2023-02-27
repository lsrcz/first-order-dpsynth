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

mss :: Num a => ConProgram a
mss =
  ConProgram
    -- suffix best
    [0, 0]
    [ ConBinary "+" (ConBinary "max" (ConUnary "zero" (ConArg 0)) (ConUnary "id" (ConArg 1))) (ConUnary "id" (ConArg 0)),
      ConBinary "max" (ConUnary "id" (ConArg 1)) (ConUnary "id" (ConArg 2))
    ]
    (ConBinary "max" (ConUnary "id" (ConArg 0)) (ConUnary "id" (ConArg 1)))
    1

mssSketchComb :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s) => proxy c -> Program s
mssSketchComb _ =
  genSymSimple
    (CombProgramSpec @c @s [0] (CombASTSpec0 1 2 ["zero", "id"] ["+", "max"]) (CombASTSpec0 0 1 [] ["max"]) 2 1)
    "mss"

mssSketchExt :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s) => proxy c -> Program s
mssSketchExt _ =
  genSymSimple
    (ExtProgramSpec @c @s [0] (CombASTSpec0 1 1 ["id", "zero"] ["+"]) "max" 2 2 2 1)
    "mss"

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
allBitStrings i = replicateM i [0 :: Int, 1]

apply :: (Num a2) => [[a2]] -> [Int] -> a2
apply [] [] = 0
apply (_ : xs) (0 : ys) = apply xs ys
apply ([x] : xs) (1 : ys) = x + apply xs ys
apply _ _ = undefined

mssSpec :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
mssSpec = spec apply allBitStrings

mssSpecV :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
mssSpecV = specV apply allBitStrings

main :: IO ()
main = do
  let config = precise z3

  mssIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "mssextV" $ synth1V config availableUnary availableBinary () (const $ con True) (mssSpecV @SymInteger) (mssSketchExt (Proxy @Integer))
  print mssIntSynthedExtV

  mssIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "msscombV" $ synth1V config availableUnary availableBinary () (const $ con True) (mssSpecV @SymInteger) (mssSketchComb (Proxy @Integer))
  print mssIntSynthedCombV
