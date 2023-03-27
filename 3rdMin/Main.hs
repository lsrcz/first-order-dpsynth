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


minSketchComb :: Program (MT SymInteger)
minSketchComb =
  genSymSimple
    (CombProgramSpec @(CT Integer) @(MT SymInteger) [CInt 0] (CombASTSpec0 1 2 0 ["zero", "id", "-"] ["&&", "||", "+", "<", "<=", "min", "max"] ["ite"]) (CombASTSpec0 0 1 0 [] ["max"] []) 3 1)
    "3ndmin"

minSpecV :: [[SymInteger]] -> SymInteger -> ExceptT VerificationConditions UnionM SymBool
minSpecV inputs v =
    mrgReturn $
        (numl <~ 3) &&~ (numle >=~ 3) &&~ (numl <~ numle)
        where
            t = head inputs
            tl = map (\x -> mrgIte (x <~ v :: SymBool) (1::SymInteger) 0) t
            tle = map (\x -> mrgIte (x <=~ v :: SymBool) (1::SymInteger) 0) t
            numl = foldl' (+) 0 tl
            numle = foldl' (+) 0 tle  

minInputSpace :: [[SymInteger]] -> SymBool
minInputSpace inputs =
    foldl' (\acc x -> acc &&~ x <=~ 0) (con True) t
        &&~ ((length t) >=~ 3)
    where
        t = head inputs

main :: IO ()
main = do
  let config = precise z3

  minIntSynthedCombV :: Maybe (ConProgram (CT Integer)) <-
    timeItAll "mincombV" $ synth1V config mtAvailableUnary mtAvailableBinary mtAvailableTernary IntValue 
      (inputSpaceMT minInputSpace) (spec2Spec minSpecV) (minSketchComb)
  print minIntSynthedCombV
