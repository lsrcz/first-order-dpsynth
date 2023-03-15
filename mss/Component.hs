module Component where

import Component.CEGIS
import Component.ConcreteMiniProg
import Component.ConcreteProg
import Component.MiniProg
import Component.Ops
import Component.Prog
import Component.QuickCheck
import Control.Monad.Except
import Data.Proxy
import Debug.Trace
import GHC.TypeLits
import Grisette
import MSSSpec
import Spec
import Test.QuickCheck
import Timing

mssComponentCProg :: Num a => CProg Integer a
mssComponentCProg =
  CProg
    [0, 0]
    [ CMiniProg
        [ CNode "zero" 3 [0],
          CNode "max" 4 [1, 3],
          CNode "+" 5 [0, 4]
        ]
        5,
      CMiniProg
        [CNode "max" 3 [1, 2]]
        3
    ]
    ( CMiniProg
        [CNode "max" 2 [0, 1]]
        2
    )

mssComponentProgSpec :: Num a => ProgSpecInit a
mssComponentProgSpec =
  ProgSpecInit
    [0, 0]
    [ MiniProgSpec
        [ ComponentSpec "zero" 1,
          ComponentSpec "max" 2,
          ComponentSpec "+" 2
        ]
        3,
      MiniProgSpec
        [ ComponentSpec "max" 2
        ]
        3
    ]
    (MiniProgSpec [ComponentSpec "max" 2] 2)

mssComponentProgSpec' :: Num a => ProgSpecInit a
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
        3,
      MiniProgSpec
        [ ComponentSpec "zero" 1,
          ComponentSpec "max" 2,
          ComponentSpec "+" 2,
          ComponentSpec "max" 2,
          ComponentSpec "+" 2
        ]
        3
    ]
    (MiniProgSpec [ComponentSpec "max" 2] 2)

mssComponentProg :: forall a. (Num a) => Prog (SymIntN 5) a
mssComponentProg = genSymSimple (mssComponentProgSpec :: ProgSpecInit a) "prog"

mssComponentProg' :: forall a. (Num a) => Prog (SymIntN 5) a
mssComponentProg' = genSymSimple (mssComponentProgSpec' :: ProgSpecInit a) "prog"

restrictedMssSpec ::
  forall a e.
  (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  [[a]] ->
  ExceptT VerificationConditions UnionM a
restrictedMssSpec l = do
  mrgTraverse_ (\x -> symAssume $ x >=~ -8 &&~ x <=~ 8) $ join l
  spec apply allBitStrings l

componentMain :: IO ()
componentMain = do
  putStrLn "MSS Component"
  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}
  quickCheck
    ( \(l :: [Integer]) ->
        (interpretCProg [toSym l] (mssComponentCProg @SymInteger) funcMap :: ExceptT VerificationConditions UnionM SymInteger)
          == mrgReturn (toSym $ mssAlgo l :: SymInteger)
    )

  Right (_, x :: CProg (IntN 5) (IntN 8)) <- timeItAll "cegis" $ cegisCustomized configb restrictedMssSpec [[[]], [["a" :: SymIntN 8]], [["a", "b"]], [["a", "b", "c"]], [["a", "b", "c", "d"]]] mssComponentProg funcMap (simpleFresh ())
  print x

  qcComponent (Proxy @(SymIntN 8)) 17 8 8 mssAlgo x

  Right (_, x :: CProg (IntN 5) (IntN 8)) <- timeItAll "cegis" $ cegisCustomized configb restrictedMssSpec [[[]], [["a" :: SymIntN 8]], [["a", "b"]], [["a", "b", "c"]], [["a", "b", "c", "d"]]] mssComponentProg' funcMap (simpleFresh ())
  print x

  qcComponent (Proxy @(SymIntN 8)) 17 8 8 mssAlgo x
