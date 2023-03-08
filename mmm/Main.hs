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
import Component.ConcreteProg
import Component.ConcreteMiniProg
import Test.QuickCheck
import Component.Ops
import Component.Prog
import Component.MiniProg
import Component.CEGIS
import Debug.Trace
import Data.List

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

mmmAlgo :: forall a. (Num a, Ord a) => [a] -> a
mmmAlgo = go 0 0 0
  where
    go ign pos neg [] = max (max ign pos) neg
    go ign pos neg (x : xs) = go (max pos neg) (max (ign + x) (neg + x)) (max (ign - x) (pos - x)) xs

isNotConsecutive :: [Int] -> Bool
isNotConsecutive [] = True
isNotConsecutive [_] = True
isNotConsecutive (1 : 1 : _) = False
isNotConsecutive (0 : 0 : _) = False
isNotConsecutive (-1 : -1 : _) = False
isNotConsecutive (_ : x : xs) = isNotConsecutive (x : xs)

allBitStrings :: Int -> [[Int]]
allBitStrings i = filter isNotConsecutive $ replicateM i [0, 1, -1]

apply :: (Show a2, Num a2) => [[a2]] -> [Int] -> a2
apply [] [] = 0
apply (_ : xs) (0 : ys) = apply xs ys
apply ([x] : xs) (1 : ys) = x + apply xs ys
apply ([x] : xs) (-1 : ys) = -x + apply xs ys
apply l r = trace (show l) $ trace (show r) $ undefined

safeApply :: (SimpleMergeable a, Num a, SafeLinearArith e a) => [[a]] -> [Int] -> ExceptT VerificationConditions UnionM a
safeApply [] [] = mrgReturn 0
safeApply (_ : xs) (0 : ys) = safeApply xs ys
safeApply ([x] : xs) (1 : ys) = do
  a <- safeApply xs ys
  safeAdd' (const AssumptionViolation) x a
safeApply ([x] : xs) (-1 : ys) = do
  a <- safeApply xs ys
  safeMinus' (const AssumptionViolation) a x
safeApply _ _ = undefined

mmmSpecV :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
mmmSpecV = specV apply allBitStrings

safeMmmSpecV :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
safeMmmSpecV = safeSpecV safeApply allBitStrings

mmmSpec :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
mmmSpec = spec apply allBitStrings

safeMmmSpec :: forall a e. (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
safeMmmSpec = safeSpec safeApply allBitStrings

cap :: (SOrd a, Num a) => [[a]] -> SymBool
cap = foldl (\acc y -> acc &&~ y >=~ -16 &&~ y <=~ 16) (con True) . join

-- Component

mmmComponentCProg :: Num a => CProg a
mmmComponentCProg =
  CProg [0, 0, 0] [
    CMiniProg [
      CNode "max" 0 [CInput 2, CInput 3]
    ] 0,
    CMiniProg [
      CNode "+" 0 [CInput 0, CInput 1],
      CNode "+" 1 [CInput 0, CInput 3],
      CNode "max" 2 [CInternal 0, CInternal 1]
    ] 2,
    CMiniProg [
      CNode "-" 0 [CInput 1, CInput 0],
      CNode "-" 1 [CInput 2, CInput 0],
      CNode "max" 2 [CInternal 0, CInternal 1]
    ] 2
  ]
  (CMiniProg [
    CNode "max" 0 [CInput 0, CInput 1],
    CNode "max" 1 [CInput 2, CInternal 0]
  ] 1)

mmmComponentProgSpec :: Num a => ProgSpecInit a
mmmComponentProgSpec = ProgSpecInit
  [0,0,0]
  [MiniProgSpec [ComponentSpec "max" 2] 4,
   MiniProgSpec [ComponentSpec "max" 2, ComponentSpec "+" 2, ComponentSpec "+" 2] 4,
   MiniProgSpec [ComponentSpec "max" 2, ComponentSpec "-" 2, ComponentSpec "-" 2] 4]
   (MiniProgSpec [ComponentSpec "max" 2, ComponentSpec "max" 2] 3)

mmmComponentProg1 :: forall a. (Num a) => Prog a
mmmComponentProg1 = genSymSimple (mmmComponentProgSpec :: ProgSpecInit a) "prog"


a :: SymInteger
a = "a"

b :: SymInteger
b = "b"

c :: SymInteger
c = "c"

d :: SymInteger
d = "d"

gen :: M SymInteger
gen = do
  f :: SymInteger =~> SymInteger =~> SymInteger {-=~> SymInteger-} <- simpleFresh ()
  mrgReturn (f # "a" # "b" {- "c"-})

input :: [SymInteger]
input = [a,b{-,c-}]

ok :: SymInteger -> SymBool
ok i = simpleMerge $ do
  v <- runExceptT $ mmmSpecV ((\x -> [x]) <$> input) i
  case v of
    Left vc -> con False
    Right sb -> return sb


rfSpec :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
rfSpec = mmmSpec . transpose


main :: IO ()
main = do
  let config = precise z3


  Right (_, r) <- cegisCustomized' (precise z3) rfSpec [input] mmmComponentProg1 funcMap gen
  print (evaluateSymToCon r (mmmComponentProg1 :: Prog SymInteger) :: CProg SymInteger)

  quickCheck (\(l :: [Integer]) -> (interpretCProg [toSym l] (mmmComponentCProg :: CProg Integer) funcMap :: ExceptT VerificationConditions UnionM SymInteger) ==
    mrgReturn (toSym $ mmmAlgo l :: SymInteger))

  mmmIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "mmmextV" $ synth1V config availableUnary availableBinary () (const $ con True) (mmmSpecV @SymInteger) (mmmSketchExt (Proxy @Integer))
  print mmmIntSynthedExtV

  mmmIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "mmmcombV" $ synth1V config availableUnary availableBinary () (const $ con True) (mmmSpecV @SymInteger) (mmmSketchComb (Proxy @Integer))
  print mmmIntSynthedCombV
