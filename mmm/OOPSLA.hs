module OOPSLA where
import Core
import Grisette
import Gen
import Timing
import Query
import Ops
import MMMSpec
import Data.Proxy

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

oopslaMain :: IO ()
oopslaMain = do
  putStrLn "-------- MMM OOPSLA --------"
  let config = precise z3
  mmmIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "mmmextV" $ synth1V config availableUnary availableBinary () (const $ con True) (mmmSpecV @SymInteger) (mmmSketchExt (Proxy @Integer))
  print mmmIntSynthedExtV

  mmmIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "mmmcombV" $ synth1V config availableUnary availableBinary () (const $ con True) (mmmSpecV @SymInteger) (mmmSketchComb (Proxy @Integer))
  print mmmIntSynthedCombV

