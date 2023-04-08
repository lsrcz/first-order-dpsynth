module Main where

import Bytecode.Instruction
import Bytecode.Prog
import Common.Spec
import Common.Timing
import Common.Val
import Component.CEGIS
import Component.ConcreteMiniProg
import Component.ConcreteProg
import Component.MiniProg
import Component.Ops
import Component.Prog
import Control.Monad
import Control.Monad.Except
import Data.Proxy
import Debug.Trace
import Grisette
import OOPSLA.Core
import OOPSLA.Gen
import OOPSLA.Ops
import OOPSLA.Query
import Test.QuickCheck
import Bytecode.Query
import Bytecode.Ops

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
    (CombProgramSpec @c @s [0] (CombASTSpec0 1 1 0 ["zero", "id"] ["+", "max"] []) (CombASTSpec0 0 1 0 [] ["max"] []) 2 1)
    "mis"

misSketchExt :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s) => proxy c -> Program s
misSketchExt _ =
  genSymSimple
    (ExtProgramSpec @c @s [0] (CombASTSpec0 1 1 0 ["zero", "id"] ["+"] []) "max" 1 2 2 1)
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

apply :: (Num a2, Show a2) => [[a2]] -> [Int] -> a2
apply [[]] [] = 0
apply [_ : xs] (0 : ys) = apply [xs] ys
apply [x : xs] (1 : ys) = x + apply [xs] ys
apply l r = trace (show l) $ trace (show r) undefined

safeApply :: (Num a, Mergeable a, SafeLinearArith e a) => [[a]] -> [Int] -> ExceptT VerificationConditions UnionM a
safeApply [[]] [] = mrgReturn 0
safeApply [_ : xs] (0 : ys) = safeApply [xs] ys
safeApply [x : xs] (1 : ys) = do
  ax <- safeApply [xs] ys
  safeAdd' (const AssumptionViolation) x ax
safeApply _ _ = undefined

misSpec :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
misSpec = spec apply allBitStrings

safeMisSpec :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
safeMisSpec = safeSpec safeApply allBitStrings

misSpecV :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
misSpecV = specV apply allBitStrings

safeMisSpecV :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
safeMisSpecV = safeSpecV safeApply allBitStrings

-- Component

misComponentCProg :: Num a => CProg CVal a
misComponentCProg =
  CProg
    (CAuxProg[0, 0]
    [ CMiniProg [CNode "+" (CInternal 0) [CInput 0, CInput 2]] (CInternal 0),
      CMiniProg [CNode "max" (CInternal 0) [CInput 1, CInput 2]] (CInternal 0)
    ])
    (CMiniProg [CNode "max" (CInternal 0) [CInput 0, CInput 1]] (CInternal 0))

misComponentProgSpec :: Num a => ProgSpecInit a
misComponentProgSpec =
  ProgSpecInit
    [0, 0]
    [ MiniProgSpec [ComponentSpec "+" 2] 3 0,
      MiniProgSpec [ComponentSpec "max" 2] 3 0
    ]
    (MiniProgSpec [ComponentSpec "max" 2] 2 0)

misComponentProg :: forall a. (Num a) => Prog SymInteger a
misComponentProg = genSymSimple (misComponentProgSpec @a) "prog"

misComponentProgSpec1 :: Num a => ProgSpecInit a
misComponentProgSpec1 =
  ProgSpecInit
    [0, 0]
    [ MiniProgSpec [ComponentSpec "+" 2, ComponentSpec "+" 2] 3 1,
      MiniProgSpec [ComponentSpec "max" 2, ComponentSpec "max" 2] 3 1
    ]
    (MiniProgSpec [ComponentSpec "max" 2] 2 0)

misComponentProg1 :: forall a. (Num a) => Prog SymInteger a
misComponentProg1 = genSymSimple (misComponentProgSpec1 @a) "prog"

misComponentProg2 :: forall a. (Num a) => Prog (SymIntN 5) a
misComponentProg2 = genSymSimple (misComponentProgSpec1 @a) "prog"

{-
misComponentProg :: Num a => Prog a
misComponentProg = Prog [0, 0] [
    MiniProg [Node "+" 0 [mrgReturn $ Input 0, mrgReturn $ Input 2]] 0,
    MiniProg [Node "max" 0 [mrgReturn $ Input 1, mrgReturn $ Input 2]] 0
   ]
   (MiniProg [Node "max" 0 [mrgReturn $ Input 0, mrgReturn $ Input 1]] 0)
   -}

a :: SymInteger
a = "a"

b :: SymInteger
b = "b"

c :: SymInteger
c = "c"

d :: SymInteger
d = "d"

gen :: M SymInteger
gen = simpleFresh () {-do
                     f :: SymInteger =~> SymInteger =~> SymInteger =~> SymInteger <- simpleFresh ()
                     mrgReturn (f # "a" # "b" # "c")-}

input :: [SymInteger]
input = [a, b, c]

-- Bytecode

bytecodeSpec :: BytecodeProgSpec ()
bytecodeSpec =
  BytecodeProgSpec
    ()
    [ BytecodeSpec [(["+", "max"], 2), (["id"], 1)] 3,
      BytecodeSpec [(["+", "max"], 2), (["id"], 1)] 3
    ]
    (BytecodeSpec [(["max"], 2)] 2)

bytecodeSketch :: BytecodeProg SymInteger
bytecodeSketch = genSymSimple bytecodeSpec "bc"

main :: IO ()
main = do
  let config = precise z3

  Just misIntSynthedBytecode :: Maybe (CBytecodeProg Integer) <-
    timeItAll "misBytecode" $ bytecodeSynth1V config 1 bytecodeFuncMap () (const $ con True) (misSpecV @SymInteger) bytecodeSketch
  print misIntSynthedBytecode

  quickCheck
    ( \(l :: [Integer]) ->
        (interpretBytecodeProg [toSym l] (toSym misIntSynthedBytecode) bytecodeFuncMap :: ExceptT VerificationConditions UnionM SymInteger)
          == mrgReturn (toSym $ misAlgo l :: SymInteger)
    )

  -- print i1

  Right (_, x :: CProg (IntN 5) (IntN 4)) <- timeItAll "cegis" $ cegisCustomized (precise boolector) safeMisSpec [[[]], [["a" :: SymIntN 4]], [["a", "b"]], [["a", "b", "c"]], [["a", "b", "c", "d"]]] misComponentProg2 funcMap (simpleFresh ())
  print x

  {-
    quickCheck
      ( \(l :: [Integer]) ->
          (interpretCProg [toSym l] x funcMap :: ExceptT VerificationConditions UnionM SymInteger)
            == mrgReturn (toSym $ misAlgo l :: SymInteger)
      )
      -}

  Right (_, x :: CProg Integer Integer) <- timeItAll "cegis" $ cegisCustomized (precise z3) misSpec [[[]], [[a]], [[a, b]], [[a, b, c]], [[a, b, c, d]]] misComponentProg1 funcMap gen

  quickCheck
    ( \(l :: [Integer]) ->
        (interpretCProg [toSym l] x funcMap :: ExceptT VerificationConditions UnionM SymInteger)
          == mrgReturn (toSym $ misAlgo l :: SymInteger)
    )

  Right (_, x :: CProg Integer Integer) <- timeItAll "cegis" $ cegisCustomized' (precise z3) misSpec [input] misComponentProg1 funcMap gen

  quickCheck
    ( \(l :: [Integer]) ->
        (interpretCProg [toSym l] x funcMap :: ExceptT VerificationConditions UnionM SymInteger)
          == mrgReturn (toSym $ misAlgo l :: SymInteger)
    )

  {-
    print (misComponentProg :: Prog SymInteger)

    quickCheck
      ( \(l :: [Integer]) ->
          (interpretCProg [toSym l] (misComponentCProg :: CProg Integer) funcMap :: ExceptT VerificationConditions UnionM SymInteger)
            == mrgReturn (toSym $ misAlgo l :: SymInteger)
      )

    let synthed :: ExceptT VerificationConditions UnionM SymInteger = interpretCProg [[1, 3, -4, 5, -6, 7]] (misComponentCProg :: CProg Integer) funcMap
    print synthed
    print (misAlgo [1, 3, -4, 5, -6, 7] :: Integer)
      -}

  misIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "misextV" $ synth1V config availableUnary availableBinary availableTernary () (const $ con True) (misSpecV @SymInteger) (misSketchExt (Proxy @Integer))
  print misIntSynthedExtV

  misIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "miscombV" $ synth1V config availableUnary availableBinary availableTernary () (const $ con True) (misSpecV @SymInteger) (misSketchComb (Proxy @Integer))
  print misIntSynthedCombV
