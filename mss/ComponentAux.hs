module ComponentAux where

import Common.Spec
import Common.Timing
import Component.ConcreteMiniProg
import Component.ConcreteProg
import Component.MiniProg
import Component.Ops
import Control.Monad.Except
import Grisette
import MSSSpec
import Test.QuickCheck
import Component.AuxProg
import Component.CEGISAux (cegisAuxQuickCheck, DistinguishingInputs (DistinguishingInputs))
import qualified Data.ByteString as B

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

mssComponentCAuxProg :: forall a. (Num a) => AuxProg B.ByteString (SymIntN 5) a
mssComponentCAuxProg = AuxProg[0, 0]
    [ MiniProg
        [ Node "zero" 3 [0],
          Node "max" 4 [1, 3],
          Node "+" 5 [0, 4]
        ]
        5
        (5,5),
      MiniProg
        [Node "max" 3 [1, 2]]
        3
        (3,3)
    ]


mssComponentAuxProgSpec :: Num a => AuxSpecInit B.ByteString a
mssComponentAuxProgSpec =
  AuxSpecInit
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

{-
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
    -}

mssComponentProg :: forall a. (Num a) => AuxProg B.ByteString (SymIntN 5) a
mssComponentProg = genSymSimple (mssComponentAuxProgSpec :: AuxSpecInit B.ByteString a) "prog"

{-
mssComponentProg' :: forall a. (Num a) => Prog (SymIntN 5) a
mssComponentProg' = genSymSimple (mssComponentProgSpec' :: ProgSpecInit a) "prog"
-}

restrictedMssSpec ::
  forall a e.
  (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  [[a]] ->
  ExceptT VerificationConditions UnionM a
restrictedMssSpec l = do
  mrgTraverse_ (\x -> symAssume $ x >=~ -8 &&~ x <=~ 8) $ join l
  spec apply allBitStrings l

mssAuxInputsGen :: Enum s => (s, s) -> Gen (DistinguishingInputs s)
mssAuxInputsGen e = do
  n <- getSize
  i1 <- vectorOf 1 (vectorOf n $ chooseEnum e)
  i2 <- vectorOf 1 (vectorOf n $ chooseEnum e)
  v <- vectorOf 1 $ chooseEnum e
  return $ DistinguishingInputs i1 i2 v

componentAuxMain :: String -> IO ()
componentAuxMain _ = do
  putStrLn "MSS Component"
  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}
  {-
  quickCheck
    ( \(l :: [Integer]) ->
        (interpretCProg [toSym l] (mssComponentCProg @SymInteger) funcMap :: ExceptT VerificationConditions UnionM SymInteger)
          == mrgReturn (toSym $ mssAlgo l :: SymInteger)
    )
    -}

  Right (_, x :: CAuxProg B.ByteString (IntN 5) (IntN 8)) <- timeItAll "cegis" $
    cegisAuxQuickCheck configb restrictedMssSpec 1 (mssAuxInputsGen (-8, 8)) 4 (mssComponentProg @(SymIntN 8)) funcMap cfuncMap (simpleFresh ())
  print x

{-
  qcComponent (Proxy @(SymIntN 8)) 17 8 8 mssAlgo x

  Right (_, x :: CProg (IntN 5) (IntN 8)) <- timeItAll "cegis" $ cegisCustomized configb restrictedMssSpec [[[]], [["a" :: SymIntN 8]], [["a", "b"]], [["a", "b", "c"]], [["a", "b", "c", "d"]]] mssComponentProg' funcMap (simpleFresh ())
  print x

  qcComponent (Proxy @(SymIntN 8)) 17 8 8 mssAlgo x
-}