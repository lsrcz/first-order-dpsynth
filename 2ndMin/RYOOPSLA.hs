module RYOOPSLA where

import OOPSLA.Core
import Data.Foldable
import OOPSLA.Gen
import Grisette
import OOPSLA.Ops
import OOPSLA.Query
import Common.T
import Common.Timing
import SecondMinSpec

minSketchComb :: Program (MT SymInteger)
minSketchComb =
  genSymSimple
    (CombProgramSpec @(CT Integer) @(MT SymInteger) [CInt 0] (CombASTSpec0 1 2 0 ["zero", "id", "-"] ["&&", "||", "+", "<", "<=", "min", "max"] ["ite"]) (CombASTSpec0 0 0 0 [] ["max"] []) 2 1)
    "2ndmin"


minInputSpace :: [[SymInteger]] -> SymBool
minInputSpace inputs =
  foldl' (\acc x -> acc &&~ x <=~ 0) (con True) t
    &&~ ((length t) >=~ 2)
  where
    t = head inputs

ryoopslaMain :: String -> IO ()
ryoopslaMain _ = do
  let config = precise z3
  minIntSynthedCombV :: Maybe (ConProgram (CT Integer)) <-
    timeItAll "mincombV" $
      synth1V
        config
        mtAvailableUnary
        mtAvailableBinary
        mtAvailableTernary
        IntValue
        (inputSpaceMT minInputSpace)
        (spec2Spec minSpecV)
        (minSketchComb)
  print minIntSynthedCombV