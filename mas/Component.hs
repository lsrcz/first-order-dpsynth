module Component where

import Common.Spec
import Common.Timing
import Component.CEGIS
import Component.ConcreteMiniProg
import Component.ConcreteProg
import Component.MiniProg
import Component.Ops
import Component.Prog
import Component.QuickCheck (qcComponent)
import Control.Monad.Except
import Data.Proxy
import Grisette
import MASSpec
import qualified Data.ByteString as B

masComponentCProg :: Num a => CProg B.ByteString Integer a
masComponentCProg =
  CProg
    (CAuxProg [0, 0, 0]
    [ CMiniProg
        [ CNode "+" 4 [0, 2],
          CNode "max" 5 [0, 4]
        ]
        5,
      CMiniProg
        [ CNode "negate" 4 [0],
          CNode "+" 5 [1, 4],
          CNode "max" 6 [4, 5]
        ]
        6,
      CMiniProg
        [ CNode "max" 4 [1, 2],
          CNode "max" 5 [3, 4]
        ]
        5
    ])
    ( CMiniProg
        [ CNode "max" 3 [0, 1],
          CNode "max" 4 [2, 3]
        ]
        4
    )

masComponentProgSpec :: Num a => ProgSpecInit B.ByteString a
masComponentProgSpec =
  ProgSpecInit
    [0, 0, 0]
    [ MiniProgSpec
        [ ComponentSpec "+" 2,
          ComponentSpec "max" 2
        ]
        4
        1,
      MiniProgSpec
        [ ComponentSpec "negate" 1,
          ComponentSpec "+" 2,
          ComponentSpec "max" 2
        ]
        4
        2,
      MiniProgSpec
        [ ComponentSpec "max" 2,
          ComponentSpec "max" 2
        ]
        4
        1
    ]
    ( MiniProgSpec
        [ ComponentSpec "max" 2,
          ComponentSpec "max" 2
        ]
        3
        1
    )

masComponentProg :: forall a. (Num a) => Prog B.ByteString (SymIntN 5) a
masComponentProg = genSymSimple (masComponentProgSpec :: ProgSpecInit B.ByteString a) "prog"

restrictedMasSpec ::
  forall a e.
  (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  [[a]] ->
  ExceptT VerificationConditions UnionM a
restrictedMasSpec l = do
  mrgTraverse_ (\x -> symAssume $ x >=~ -8 &&~ x <=~ 8) $ join l
  spec apply allBitStrings l

componentMain :: String -> IO ()
componentMain _ = do
  putStrLn "MAS Component"
  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}
  qcComponent (Proxy @SymInteger) 17 8 8 masAlgo masComponentCProg

  Right (_, x :: CProg B.ByteString (IntN 5) (IntN 8)) <- timeItAll "cegis" $ cegisCustomized configb restrictedMasSpec [[[]], [["a" :: SymIntN 8]], [["a", "b"]], [["a", "b", "c"]], [["a", "b", "c", "d"]]] masComponentProg funcMap (simpleFresh ())
  print x

  qcComponent (Proxy @(SymIntN 8)) 17 8 8 masAlgo x
