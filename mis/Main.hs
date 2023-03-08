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
import Component.CEGIS
import Component.Ops
import Test.QuickCheck
import Component.Prog
import Component.MiniProg
import Control.Monad.Trans.Writer
import Data.Bifunctor
import Debug.Trace
import Data.List

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
    (CombProgramSpec @c @s [0] (CombASTSpec0 1 1 ["zero", "id"] ["+", "max"]) (CombASTSpec0 0 1 [] ["max"]) 2 1)
    "mis"

misSketchExt :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s) => proxy c -> Program s
misSketchExt _ =
  genSymSimple
    (ExtProgramSpec @c @s [0] (CombASTSpec0 1 1 ["zero", "id"] ["+"]) "max" 1 2 2 1)
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
apply [] [] = 0
apply (_ : xs) (0 : ys) = apply xs ys
apply ([x] : xs) (1 : ys) = x + apply xs ys
apply l r = trace (show l) $ trace (show r) undefined

safeApply :: (Num a, Mergeable a, SafeLinearArith e a) => [[a]] -> [Int] -> ExceptT VerificationConditions UnionM a
safeApply [] [] = mrgReturn 0
safeApply (_ : xs) (0 : ys) = safeApply xs ys
safeApply ([x] : xs) (1 : ys) = do
  a <- safeApply xs ys
  safeAdd' (const AssumptionViolation) x a
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

misComponentCProg :: Num a => CProg a
misComponentCProg =
  CProg [0, 0] [
    CMiniProg [CNode "+" 0 [CInput 0, CInput 2]] 0,
    CMiniProg [CNode "max" 0 [CInput 1, CInput 2]] 0
   ]
   (CMiniProg [CNode "max" 0 [CInput 0, CInput 1]] 0)

misComponentProgSpec :: ProgSpec
misComponentProgSpec = ProgSpec
  [MiniProgSpec [ComponentSpec "+" 2] 3,
   MiniProgSpec [ComponentSpec "max" 2] 3]
   (MiniProgSpec [ComponentSpec "max" 2] 2)

misComponentProg :: (GenSymSimple () a, Num a) => Prog a
misComponentProg = genSymSimple ((), misComponentProgSpec) "prog"

misComponentProgSpec1 :: ProgSpec
misComponentProgSpec1 = ProgSpec
  [MiniProgSpec [ComponentSpec "+" 2, ComponentSpec "-" 2] 3,
   MiniProgSpec [ComponentSpec "max" 2, ComponentSpec "min" 2] 3]
   (MiniProgSpec [ComponentSpec "max" 2] 2)

misComponentProg1 :: (GenSymSimple () a, Num a) => Prog a
misComponentProg1 = genSymSimple ((), misComponentProgSpec1) "prog"



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

gen :: M SymInteger
gen = do
  f :: SymInteger =~> SymInteger =~> SymInteger =~> SymInteger <- simpleFresh ()
  mrgReturn (f # "a" # "b" # "c")

input :: [SymInteger]
input = [a,b,c]

ok :: SymInteger -> SymBool
ok i = simpleMerge $ do
  v <- runExceptT $ misSpecV [input] i
  case v of
    Left vc -> con False
    Right sb -> con True

int = simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT (interpretProg [input] misComponentProg funcMap gen) "int"

i1 :: UnionM (Either VerificationConditions SymInteger)
i1 = fst int


rfSpec :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
rfSpec = misSpec . transpose

main :: IO ()
main = do
  let config = precise z3

  -- print i1

  Right (_, r) <- timeItAll "cegis" $ cegisCustomized' (precise z3) rfSpec [input] misComponentProg1 funcMap gen
  -- print r
  let x = evaluateSymToCon r (misComponentProg1 :: Prog SymInteger) :: CProg Integer
  print x

  quickCheck (\(l :: [Integer]) -> (interpretCProg [toSym l] (x :: CProg Integer) funcMap :: ExceptT VerificationConditions UnionM SymInteger) ==
    mrgReturn (toSym $ misAlgo l :: SymInteger))

  print (misComponentProg :: Prog SymInteger)

  quickCheck (\(l :: [Integer]) -> (interpretCProg [toSym l] (misComponentCProg :: CProg Integer) funcMap :: ExceptT VerificationConditions UnionM SymInteger) ==
    mrgReturn (toSym $ misAlgo l :: SymInteger))

  let x :: ExceptT VerificationConditions UnionM SymInteger = interpretCProg [[1,3,-4,5,-6,7]] (misComponentCProg :: CProg Integer) funcMap
  print x
  print (misAlgo [1,3,-4,5,-6,7] :: Integer)

  misIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "misextV" $ synth1V config availableUnary availableBinary () (const $ con True) (misSpecV @SymInteger) (misSketchExt (Proxy @Integer))
  print misIntSynthedExtV

  misIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "miscombV" $ synth1V config availableUnary availableBinary () (const $ con True) (misSpecV @SymInteger) (misSketchComb (Proxy @Integer))
  print misIntSynthedCombV
