module OOPSLA where

import Core
import Data.Proxy
import Gen
import Grisette
import Interpreter
import MASSpec
import Ops
import Query
import Test.QuickCheck
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

oopslaMain :: IO ()
oopslaMain = do
  let config = precise z3

  Just masIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "masextV" $ synth1V config availableUnary availableBinary () (const $ con True) (masSpecV @SymInteger) (masSketchExt (Proxy @Integer))
  print masIntSynthedExtV

  quickCheck (\(l :: [Integer]) -> interpretSketch availableUnary availableBinary (toSym masIntSynthedExtV) [toSym l] == mrgReturn (toSym $ masAlgo l :: SymInteger))

  Just masIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "mascombV" $ synth1V config availableUnary availableBinary () (const $ con True) (masSpecV @SymInteger) (masSketchComb (Proxy @Integer))
  print masIntSynthedCombV
