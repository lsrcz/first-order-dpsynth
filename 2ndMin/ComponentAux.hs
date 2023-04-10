module ComponentAux where
import Component.ConcreteProg
import Component.ConcreteMiniProg
import Common.T
import Component.QuickCheck (qcTComponent)
import Grisette
import SecondMinSpec
import Component.AuxProg
import Component.Prog
import Component.MiniProg
import Test.QuickCheck
import Common.Timing
import Component.CEGIS
import Component.Ops
import qualified Data.ByteString as B

secondMinComponentCProg :: Num a => CProg B.ByteString (IntN 5) (CT a)
secondMinComponentCProg =
  CProg
    (CAuxProg[CInt 0, CInt 0]
    [ CMiniProg
      [ CNode "min" 3 [0, 1]]
      3,
      CMiniProg
      [ CNode "max" 3 [0, 1],
        CNode "min" 4 [2, 3]]
      4])
    ( CMiniProg [] 1)

secondMinComponentProg0 :: (Mergeable a, Num a) => Prog B.ByteString (SymIntN 5) (MT a)
secondMinComponentProg0 =
  Prog
    (AuxProg [mrgReturn $ TInt 0, mrgReturn $ TInt 0]
    [ MiniProg
      [ Node "min" 3 [0, 1]]
      3
      (3, 3),
      MiniProg
      [ Node "max" 3 [0, 1],
        Node "min" 4 [2, 3]]
      4
      (4, 4)])
    ( MiniProg [] 1 (1,1))

secondMinComponentProgSpec :: (Mergeable a, Num a) => ProgSpecInit B.ByteString (MT a)
secondMinComponentProgSpec =
  ProgSpecInit
    [mrgReturn $ TInt 0, mrgReturn $ TInt 0]
    [ MiniProgSpec
      [ComponentSpec "min" 2]
      3
      0,
      MiniProgSpec
      [ComponentSpec "max" 2,
       ComponentSpec "min" 2]
      3
      1
      ]
    ( MiniProgSpec [] 2 0)

secondMinComponentProgSpec' :: (Mergeable a, Num a) => ProgSpecInit B.ByteString (MT a)
secondMinComponentProgSpec' =
  ProgSpecInit
    [mrgReturn $ TInt 0, mrgReturn $ TInt 0]
    [ MiniProgSpec
      [ComponentSpec "max" 2,
       --ComponentSpec "max" 2,
       ComponentSpec "+" 2,
       ComponentSpec "-" 2,
       --ComponentSpec "min" 2,
       ComponentSpec "min" 2]
      3
      3,
      MiniProgSpec
      [ComponentSpec "max" 2,
       --ComponentSpec "max" 2,
       ComponentSpec "+" 2,
       ComponentSpec "-" 2,
       --ComponentSpec "min" 2,
       ComponentSpec "min" 2]
      3
      3
      ]
    ( MiniProgSpec
      [ComponentSpec "max" 2,
       --ComponentSpec "max" 2,
       ComponentSpec "+" 2,
       ComponentSpec "-" 2,
       --ComponentSpec "min" 2,
       ComponentSpec "min" 2]
      3
      3)

secondMinComponentProg :: forall a. (Num a, Mergeable a) => Prog B.ByteString (SymIntN 5) (MT a)
secondMinComponentProg = genSymSimple (secondMinComponentProgSpec :: ProgSpecInit B.ByteString (MT a)) "prog"

secondMinInputsGen :: Enum s => (s, s) -> Gen [[CT s]]
secondMinInputsGen e = do
  n <- getSize
  vectorOf 1 (vectorOf n $ CInt <$> chooseEnum e)

componentAuxMain :: String -> IO ()
componentAuxMain _ = do
  -- qcTComponent (Proxy @SymInteger) 17 16 2 4 secondMin secondMinComponentCProg 

  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}
  Right (_, x :: CProg B.ByteString (IntN 5) (CT (IntN 8))) <-
    timeItAll "cegis" $
      cegisQuickCheckAssert
        configb
        (spec2Spec' @(SymIntN 8) minSpec)
        1
        (secondMinInputsGen (-16, 0))
        4
        secondMinComponentProg
        mtfuncMap
        mtcfuncMap
        (simpleFresh ())
  print x

  qcTComponent 17 16 2 4 secondMin x

