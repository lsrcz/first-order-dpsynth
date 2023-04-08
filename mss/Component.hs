module Component where

import Common.Spec
import Common.Timing
import Component.CEGIS
import Component.ConcreteMiniProg
import Component.ConcreteProg
import Component.MiniProg
import Component.Ops
import Component.Prog
import Component.QuickCheck
import Control.Monad.Except
import Data.Proxy
import Grisette
import MSSSpec
import qualified Data.ByteString as B
import Test.QuickCheck

mssComponentCProg :: Num a => CProg B.ByteString Integer a
mssComponentCProg =
  CProg
    (CAuxProg[0, 0]
    [ CMiniProg
        [ CNode "zero" 3 [0],
          CNode "max" 4 [1, 3],
          CNode "+" 5 [0, 4]
        ]
        5,
      CMiniProg
        [CNode "max" 3 [1, 2]]
        3
    ])
    ( CMiniProg
        [CNode "max" 2 [0, 1]]
        2
    )

mssComponentCProg' :: Num a => CProg B.ByteString Integer a
mssComponentCProg' =
  CProg
    (CAuxProg[0, 0]
    [ CMiniProg
        [ CNode "zero" 3 [0],
          CNode "+" 4 [0, 1],
          CNode "max" 5 [3, 4]
        ]
        5,
      CMiniProg
        [CNode "max" 3 [1, 2]]
        3
    ])
    ( CMiniProg
        [CNode "max" 2 [0, 1]]
        2
    )

mssComponentProgSpec :: Num a => ProgSpecInit B.ByteString a
mssComponentProgSpec =
  ProgSpecInit
    [0, 0]
    [ MiniProgSpec
        [ ComponentSpec "zero" 1,
          ComponentSpec "max" 2,
          ComponentSpec "+" 2
        ]
        3
        2,
      MiniProgSpec
        [ ComponentSpec "max" 2
        ]
        3
        0
    ]
    (MiniProgSpec [ComponentSpec "max" 2] 2 0)

mssComponentProgSpec' :: Num a => ProgSpecInit B.ByteString a
mssComponentProgSpec' =
  ProgSpecInit
    [0, 0]
    [ MiniProgSpec
        [ ComponentSpec "zero" 1,
          ComponentSpec "max" 2,
          ComponentSpec "+" 2,
          ComponentSpec "max" 2,
          ComponentSpec "+" 2
        ]
        3
        2,
      MiniProgSpec
        [ ComponentSpec "zero" 1,
          ComponentSpec "max" 2,
          ComponentSpec "+" 2,
          ComponentSpec "max" 2,
          ComponentSpec "+" 2
        ]
        3
        0
    ]
    (MiniProgSpec [ComponentSpec "max" 2] 2 0)

mssComponentProg :: forall a. (Num a) => Prog B.ByteString (SymIntN 5) a
mssComponentProg = genSymSimple (mssComponentProgSpec :: ProgSpecInit B.ByteString a) "prog"

mssComponentProg' :: forall a. (Num a) => Prog B.ByteString (SymIntN 5) a
mssComponentProg' = genSymSimple (mssComponentProgSpec' :: ProgSpecInit B.ByteString a) "prog"

restrictedMssSpec ::
  forall a e.
  (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  [[a]] ->
  ExceptT VerificationConditions UnionM a
restrictedMssSpec l = do
  mrgTraverse_ (\x -> symAssume $ x >=~ -8 &&~ x <=~ 8) $ join l
  spec apply allBitStrings l

componentMain :: String -> IO ()
componentMain _ = do
  putStrLn "MSS Component"
  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}
  quickCheck
    ( \(l :: [Integer]) ->
        (interpretCProg [toSym l] (mssComponentCProg' @SymInteger) funcMap :: ExceptT VerificationConditions UnionM SymInteger)
          == mrgReturn (toSym $ mssAlgo l :: SymInteger)
    )

  Right (_, x :: CProg B.ByteString (IntN 5) (IntN 8)) <- timeItAll "cegis" $ cegisCustomized configb restrictedMssSpec [[[]], [["a" :: SymIntN 8]], [["a", "b"]], [["a", "b", "c"]], [["a", "b", "c", "d"]]] mssComponentProg funcMap (simpleFresh ())
  print x

  qcComponent (Proxy @(SymIntN 8)) 17 8 8 mssAlgo x

  Right (_, x :: CProg B.ByteString (IntN 5) (IntN 8)) <- timeItAll "cegis" $ cegisCustomized configb restrictedMssSpec [[[]], [["a" :: SymIntN 8]], [["a", "b"]], [["a", "b", "c"]], [["a", "b", "c", "d"]]] mssComponentProg' funcMap (simpleFresh ())
  print x

  qcComponent (Proxy @(SymIntN 8)) 17 8 8 mssAlgo x
