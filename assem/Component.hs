module Component where

import ASSEMSpec
import Component.CEGIS
import Component.ConcreteMiniProg
import Component.ConcreteProg
import Component.MiniProg
import Component.Ops
import Component.Prog
import Component.QuickCheck (qcComponent4)
import Control.Monad.Except
import Data.List
import Data.Proxy
import Debug.Trace
import Grisette
import Timing
import Test.QuickCheck.Gen
import Test.QuickCheck (Arbitrary(arbitrary))

assemComponentCProg :: Num a => CProg Integer a
assemComponentCProg =
  CProg
    [0, 0]
    [ CMiniProg
        [ CNode "+" 6 [0, 4],
          CNode "+" 7 [1, 5],
          CNode "min" 8 [6, 7]
        ]
        8,
      CMiniProg
        [ CNode "+" 6 [2, 5],
          CNode "+" 7 [3, 4],
          CNode "min" 8 [6, 7]
        ]
        8
    ]
    ( CMiniProg
        [ CNode "min" 2 [0, 1]
        ]
        2
    )

assemComponentProgSpec :: Num a => ProgSpecInit a
assemComponentProgSpec =
  ProgSpecInit
    [0, 0]
    [ MiniProgSpec
        [ ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "min" 2
        ]
        6,
      MiniProgSpec
        [ ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "min" 2
        ]
        6
    ]
    ( MiniProgSpec
        [ComponentSpec "min" 2]
        2
    )

assemComponentProgSpec' :: Num a => ProgSpecInit a
assemComponentProgSpec' =
  ProgSpecInit
    [0, 0]
    [ MiniProgSpec
        [ ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "min" 2,
          ComponentSpec "min" 2
        ]
        6,
      MiniProgSpec
        [ ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "min" 2,
          ComponentSpec "min" 2
        ]
        6
    ]
    ( MiniProgSpec
        [ComponentSpec "min" 2]
        2
    )

assemComponentProg :: forall a. (Num a) => Prog (SymIntN 5) a
assemComponentProg = genSymSimple (assemComponentProgSpec :: ProgSpecInit a) "prog"

assemComponentProg' :: forall a. (Num a) => Prog (SymIntN 5) a
assemComponentProg' = genSymSimple (assemComponentProgSpec' :: ProgSpecInit a) "prog"

restrictedAssemSpec ::
  forall a e.
  (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  [[a]] ->
  ExceptT VerificationConditions UnionM a
restrictedAssemSpec inputs = do
  mrgTraverse_ (\x -> symAssume $ x >=~ -8 &&~ x <=~ 8) $ join inputs
  mrgReturn $ trav specs
  where
    specs = sort $ allSpec (length $ head inputs) 1 ++ allSpec (length $ head inputs) 2
    trav [] = undefined
    trav [v] = apply inputs v
    trav (v : vs) = let a = apply inputs v; acc = trav vs in mrgIte (a <=~ acc) a acc

assemInputsGen :: Enum s => (s, s) -> Gen [[s]]
assemInputsGen e = do
  n <- getSize
  vectorOf 4 (vectorOf n $ chooseEnum e)

componentMain :: IO ()
componentMain = do
  putStrLn "MAS Component"
  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}
  qcComponent4 (Proxy @SymInteger) 17 8 8 assemAlgo assemComponentCProg

  Right (_, x :: CProg (IntN 5) (IntN 8)) <-
    timeItAll "cegis" $
      cegisQuickCheck
        configb
        (restrictedAssemSpec @(SymIntN 8))
        4
        (assemInputsGen (-8, 8))
        4
        assemComponentProg
        funcMap
        (simpleFresh ())
  print x

  qcComponent4 (Proxy @(SymIntN 8)) 17 8 8 assemAlgo x

{-

  Right (_, x :: CProg (IntN 5) (IntN 8)) <-
    timeItAll "cegis" $
      cegisCustomized
        configb
        restrictedAssemSpec
        [ [[], [], [], []],
          [["a1" :: SymIntN 8], ["a2"], ["a3"], ["a4"]],
          [["a1", "b1"], ["a2", "b2"], ["a3", "b3"], ["a4", "b4"]],
          [["a1", "b1", "c1"], ["a2", "b2", "c2"], ["a3", "b3", "c3"], ["a4", "b4", "c4"]],
          [["a1", "b1", "c1", "d1"], ["a2", "b2", "c2", "d2"], ["a3", "b3", "c3", "d3"], ["a4", "b4", "c4", "d4"]]
        ]
        assemComponentProg
        funcMap
        (simpleFresh ())
  print x

  qcComponent4 (Proxy @(SymIntN 8)) 17 8 8 assemAlgo x
-}