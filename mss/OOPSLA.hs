module OOPSLA where

import Core
import Data.Proxy
import Gen
import Grisette
import MSSSpec
import Ops
import Query
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

oopslaMain :: IO ()
oopslaMain = do
  let config = precise z3

  mssIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "mssextV" $ synth1V config availableUnary availableBinary () (const $ con True) (mssSpecV @SymInteger) (mssSketchExt (Proxy @Integer))
  print mssIntSynthedExtV

  mssIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "msscombV" $ synth1V config availableUnary availableBinary () (const $ con True) (mssSpecV @SymInteger) (mssSketchComb (Proxy @Integer))
  print mssIntSynthedCombV
