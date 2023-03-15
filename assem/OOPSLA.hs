module OOPSLA where

import ASSEMSpec
import Control.Monad.Except
import Core
import Data.Proxy
import Gen
import Grisette
import Interpreter
import Ops
import Query
import Test.QuickCheck
import Timing

assem :: Num a => ConProgram a
assem =
  ConProgram
    -- stay1 switch1 stay2 switch2
    [0, 0]
    [ ConBinary
        "min"
        (ConBinary "+" (ConArg 4) (ConArg 0))
        (ConBinary "+" (ConArg 5) (ConArg 1)),
      ConBinary
        "min"
        (ConBinary "+" (ConArg 5) (ConArg 2))
        (ConBinary "+" (ConArg 4) (ConArg 3))
    ]
    (ConBinary "min" (ConArg 0) (ConArg 1))
    -- stay switch
    4

assemSketchComb :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s, Show s) => proxy c -> Program s
assemSketchComb _ =
  genSymSimple
    (CombProgramSpec @c @s [0] (CombASTSpec0 1 3 ["zero", "id"] ["+", "min"]) (CombASTSpec0 0 1 [] ["min"]) 2 4)
    "assem"

assemSketchExt :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s, Show s) => proxy c -> Program s
assemSketchExt _ =
  genSymSimple
    (ExtProgramSpec @c @s [0] (CombASTSpec0 1 1 ["zero", "id"] ["+"]) "min" 2 2 2 4)
    "assemopt"

cap :: (SOrd a, Num a) => [[a]] -> SymBool
cap = foldl (\acc y -> acc &&~ y >=~ -16 &&~ y <=~ 16) (con True) . join

px :: [(Integer, Integer, Integer, Integer)] -> [[Integer]]
px [] = [[], [], [], []]
px ((a, b, c, d) : xs) = case px xs of
  [as, bs, cs, ds] -> [a : as, b : bs, c : cs, d : ds]
  _ -> undefined

oopslaMain :: IO ()
oopslaMain = do
  let config = precise z3

  Just assemIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "assembextV" $ synth1V config availableUnary availableBinary () (const $ con True) (assemSpecV @SymInteger) (assemSketchExt (Proxy @Integer))
  print assemIntSynthedExtV

  quickCheck
    ( \(l :: [(Integer, Integer, Integer, Integer)]) ->
        interpretSketch availableUnary availableBinary (toSym assemIntSynthedExtV) (toSym $ px l) == mrgReturn (toSym $ assemAlgo (px l) :: SymInteger)
    )

  assemIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "assembcombV" $ synth1V config availableUnary availableBinary () (const $ con True) (assemSpecV @SymInteger) (assemSketchComb (Proxy @Integer))
  print assemIntSynthedCombV
