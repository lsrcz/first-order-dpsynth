module Component where

import Common.Spec
import Common.Timing
import Common.Val
import Component.CEGIS
import Component.ConcreteMiniProg
import Component.ConcreteProg
import Component.MiniProg
import Component.Ops
import Component.Prog
import Component.QuickCheck
import Control.Monad
import Control.Monad.Except
import Data.Proxy
import Grisette
import MMMSpec
import Test.QuickCheck

mmmComponentCProg :: Num a => CProg CVal a
mmmComponentCProg =
  CProg
    (CAuxProg [0, 0, 0]
    [ CMiniProg
        [ CNode "max" (CInternal 0) [CInput 2, CInput 3]
        ]
        (CInternal 0),
      CMiniProg
        [ CNode "+" (CInternal 0) [CInput 0, CInput 1],
          CNode "+" (CInternal 1) [CInput 0, CInput 3],
          CNode "max" (CInternal 2) [CInternal 0, CInternal 1]
        ]
        (CInternal 2),
      CMiniProg
        [ CNode "-" (CInternal 0) [CInput 1, CInput 0],
          CNode "-" (CInternal 1) [CInput 2, CInput 0],
          CNode "max" (CInternal 2) [CInternal 0, CInternal 1]
        ]
        (CInternal 2)
    ])
    ( CMiniProg
        [ CNode "max" (CInternal 0) [CInput 0, CInput 1],
          CNode "max" (CInternal 1) [CInput 2, CInternal 0]
        ]
        (CInternal 1)
    )

mmmComponentCProg' :: Num a => CProg Integer a
mmmComponentCProg' =
  CProg
    (CAuxProg [0, 0, 0]
    [ CMiniProg
        [ CNode "max" 4 [2, 3]
        ]
        4,
      CMiniProg
        [ CNode "+" 4 [1, 1],
          CNode "max" 5 [3, 1],
          CNode "+" 6 [5, 0]
        ]
        6,
      CMiniProg
        [ CNode "-" 4 [1, 0],
          CNode "-" 5 [2, 0],
          CNode "max" 6 [5, 4]
        ]
        6
    ])
    ( CMiniProg
        [ CNode "max" 3 [0, 2],
          CNode "max" 4 [1, 3]
        ]
        4
    )

mmmComponentProgSpec :: Num a => ProgSpecInit a
mmmComponentProgSpec =
  ProgSpecInit
    [0, 0, 0]
    [ MiniProgSpec [ComponentSpec "max" 2] 4 0,
      MiniProgSpec
        [ RestrictedSpec "max" 2 (Just [2]) (Just [Internal 0, Internal 1]),
          RestrictedSpec "max" 2 (Just [3]) (Just [Internal 0, Internal 1]),
          RestrictedSpec "+" 2 (Just [1]) Nothing,
          RestrictedSpec "+" 2 (Just [0]) Nothing
        ]
        4
        2,
      MiniProgSpec
        [ RestrictedSpec "max" 2 (Just [2]) (Just [Internal 0, Internal 1]),
          RestrictedSpec "max" 2 (Just [3]) (Just [Internal 0, Internal 1]),
          RestrictedSpec "-" 2 (Just [1]) Nothing,
          RestrictedSpec "-" 2 (Just [0]) Nothing
        ]
        4
        2
    ]
    (MiniProgSpec [ComponentSpec "max" 2, ComponentSpec "max" 2] 3 1)

mmmComponentProg1 :: forall a. (Num a) => Prog (UnionM Val) a
mmmComponentProg1 = genSymSimple (mmmComponentProgSpec :: ProgSpecInit a) "prog"

mmmComponentProg1' :: forall a. (Num a) => Prog SymInteger a
mmmComponentProg1' = genSymSimple (mmmComponentProgSpec :: ProgSpecInit a) "prog"

mmmComponentProg1'' :: forall a. (Num a) => Prog (SymIntN 5) a
mmmComponentProg1'' = genSymSimple (mmmComponentProgSpec :: ProgSpecInit a) "prog"

restrictedMmmSpec ::
  forall a e.
  (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  [[a]] ->
  ExceptT VerificationConditions UnionM a
restrictedMmmSpec l = do
  mrgTraverse_ (\x -> symAssume $ x >=~ -8 &&~ x <=~ 8) $ join l
  spec apply allBitStrings l

mmmInputsGen :: Enum s => (s, s) -> Gen [[s]]
mmmInputsGen e = do
  n <- getSize
  vectorOf 1 (vectorOf n $ chooseEnum e)

componentMain :: String -> IO ()
componentMain _ = do
  let config = precise z3 {Grisette.transcript = Just "a.smt2"}

  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}

  Right (_, x :: CProg (IntN 5) (IntN 8)) <-
    timeItAll "cegis" $
      cegisQuickCheckAssert
        configb
        (restrictedMmmSpec @(SymIntN 8))
        1
        (mmmInputsGen (-8, 8))
        4
        mmmComponentProg1''
        funcMap
        (simpleFresh ())
  print x

  qcComponent (Proxy @(SymIntN 8)) 17 8 8 mmmAlgo x



  Right (_, x :: CProg (IntN 5) (IntN 8)) <- timeItAll "cegis" $ cegisCustomized configb restrictedMmmSpec [[[]], [[-1]], [[1]], [[-1, 1]], [[1,1]], [[7]], [[1,-6]], [[7,2]], [[1,-6,2]], [[2,0,2]], [[2,0,2,1]], [[-3,1]], [[-3,1,1]], [["a" :: SymIntN 8]], [["a", "b"]], [["a", "b", "c"]], [["a", "b", "c", "d"]]] mmmComponentProg1'' funcMap (simpleFresh ())
  print x

  qcComponent (Proxy @(SymIntN 8)) 17 8 8 mmmAlgo x

  Right (_, x :: CProg Integer Integer) <- cegisCustomized config mmmSpec [[[]], [["a" :: SymInteger]], [["a", "b"]], [["a", "b", "c"]], [["a", "b", "c", "d"]]] mmmComponentProg1' funcMap (simpleFresh ())

  print x
  quickCheck
    ( \(l :: [Integer]) ->
        (interpretCProg [toSym l] x funcMap :: ExceptT VerificationConditions UnionM SymInteger)
          == mrgReturn (toSym $ mmmAlgo l :: SymInteger)
    )

  Right (_, x :: CProg CVal Integer) <- cegisCustomized config mmmSpec [[[]], [["a" :: SymInteger]], [["a", "b"]], [["a", "b", "c"]], [["a", "b", "c", "d"]]] mmmComponentProg1 funcMap (simpleFresh ())

  print x
  quickCheck
    ( \(l :: [Integer]) ->
        (interpretCProg [toSym l] x funcMap :: ExceptT VerificationConditions UnionM SymInteger)
          == mrgReturn (toSym $ mmmAlgo l :: SymInteger)
    )

  Right (_, x :: CProg CVal Integer) <- cegisCustomized' config mmmSpec [["a" :: SymInteger, "b", "c"]] mmmComponentProg1 funcMap (simpleFresh ())
  print x
  quickCheck
    ( \(l :: [Integer]) ->
        (interpretCProg [toSym l] x funcMap :: ExceptT VerificationConditions UnionM SymInteger)
          == mrgReturn (toSym $ mmmAlgo l :: SymInteger)
    )

  quickCheck
    ( \(l :: [Integer]) ->
        (interpretCProg [toSym l] (mmmComponentCProg :: CProg CVal Integer) funcMap :: ExceptT VerificationConditions UnionM SymInteger)
          == mrgReturn (toSym $ mmmAlgo l :: SymInteger)
    )
