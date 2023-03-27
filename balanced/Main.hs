module Main where

import Control.Monad.Except
import OOPSLA.Core
import Data.Foldable
import OOPSLA.Gen
import Grisette
import OOPSLA.Ops
import OOPSLA.Query
import Common.T
import Common.Timing
import GHC.Stack
import Debug.Trace

balancedSketchComb :: Program (MT SymInteger)
balancedSketchComb =
  genSymSimple
    (CombProgramSpec @(CT Integer) @(MT SymInteger) [CInt 0, CInt 1] (CombASTSpec0 1 2 1 ["zero", "id", "one", "-"] ["&&", "||", "+", "<", "<="] ["ite"]) (CombASTSpec0 0 0 0 [] [] []) 2 1)
    "balanced"

isConsecutive1 :: [Int] -> Bool
isConsecutive1 [] = True
isConsecutive1 (1 : xs) = isConsecutive1 xs
isConsecutive1 (0 : xs) = all (== 0) xs
isConsecutive1 (_ : _) = undefined

allBitStrings :: Int -> [[Int]]
allBitStrings i = filter isConsecutive1 $ replicateM i [0 :: Int, 1]

apply :: (Show a2, HasCallStack, Num a2) => [[a2]] -> [Int] -> a2
apply [[]] [] = 0
apply [_ : xs] (0 : ys) = apply [xs] ys
apply [x : xs] (1 : ys) = x + apply [xs] ys
apply _ _ = undefined

balancedSpecV :: forall a. (Num a, SOrd a, SimpleMergeable  a, Show a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
balancedSpecV inputs v =
    mrgReturn $
        result &&~ (v ==~ 1) ||~ (result ==~ (con False)) &&~ (v ==~ 0)
    where
        result = foldl' (\acc x -> acc &&~ x >=~ 0) (con True) t
        t = map (\x -> apply inputs x) (allBitStrings (length $ head inputs))

balancedInputSpace :: forall a. (Num a, SOrd a, SimpleMergeable a) => [[a]] -> SymBool
balancedInputSpace inputs =
    foldl' (\acc x -> acc &&~ x >=~ -1 &&~ x <=~ 1) (con True) t
    where
        t = head inputs

main :: IO ()
main = do
  let config = precise z3

  balancedIntSynthedCombV :: Maybe (ConProgram (CT Integer)) <-
    timeItAll "balancedcombV" $ synth1V config mtAvailableUnary mtAvailableBinary mtAvailableTernary IntValue (inputSpaceMT balancedInputSpace) (spec2Spec balancedSpecV) (balancedSketchComb)
  print balancedIntSynthedCombV
