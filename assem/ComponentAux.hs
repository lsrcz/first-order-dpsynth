module ComponentAux where

import ASSEMSpec
import Common.Timing
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
import Grisette
import Test.QuickCheck
import Component.AuxProg
import Component.CEGISAux

assemComponentCProg :: Num a => CProg Integer a
assemComponentCProg =
  CProg
    (CAuxProg[0, 0]
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
    ])
    ( CMiniProg
        [ CNode "min" 2 [0, 1]
        ]
        2
    )

assemComponentProgAuxSpec :: Num a => AuxSpecInit a
assemComponentProgAuxSpec =
  AuxSpecInit
    [0, 0]
    [ MiniProgSpec
        [ ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "-" 2,
          ComponentSpec "-" 2,
          ComponentSpec "min" 2
        ]
        6
        2,
      MiniProgSpec
        [ ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "-" 2,
          ComponentSpec "-" 2,
          ComponentSpec "min" 2
        ]
        6
        2
    ]

assemComponentProg :: forall a. (Num a) => AuxProg (SymIntN 5) a
assemComponentProg = genSymSimple (assemComponentProgAuxSpec :: AuxSpecInit a) "prog"

{-
assemComponentProgSpec' :: Num a => ProgSpecInit a
assemComponentProgSpec' =
  ProgSpecInit
    [0, 0]
    [ MiniProgSpec
        [ ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "-" 2,
          ComponentSpec "-" 2,
          ComponentSpec "min" 2,
          ComponentSpec "max" 2
        ]
        6
        2,
      MiniProgSpec
        [ ComponentSpec "+" 2,
          ComponentSpec "+" 2,
          ComponentSpec "-" 2,
          ComponentSpec "-" 2,
          ComponentSpec "min" 2,
          ComponentSpec "max" 2
        ]
        6
        2
    ]
    ( MiniProgSpec
        [ComponentSpec "min" 2]
        2
        0
    )

assemComponentProg' :: forall a. (Num a) => Prog (SymIntN 5) a
assemComponentProg' = genSymSimple (assemComponentProgSpec' :: ProgSpecInit a) "prog"
-}

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

assemAuxInputsGen :: Enum s => (s, s) -> Gen (DistinguishingInputs s)
assemAuxInputsGen e = do
  n <- getSize
  i1 <- vectorOf 4 (vectorOf n $ chooseEnum e)
  i2 <- vectorOf 4 (vectorOf n $ chooseEnum e)
  v <- vectorOf 4 $ chooseEnum e
  return $ DistinguishingInputs i1 i2 v

componentAuxMain :: String -> IO ()
componentAuxMain _ = do
  putStrLn "MAS Component"
  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}

  Right (_, x :: CAuxProg (IntN 5) (IntN 8)) <-
    timeItAll "cegis" $
      cegisAuxQuickCheck
        configb
        (restrictedAssemSpec @(SymIntN 8))
        4
        (assemAuxInputsGen (-8, 8))
        4
        assemComponentProg
        funcMap
        (simpleFresh ())
  print x
