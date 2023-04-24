module ComponentList where
import Component.ConcreteMiniProg
import Component.ListAuxProg
import Component.ListCombProg
import Component.ListComb2Prog
import Component.CEGISListComb2
import Component.ListOps
import Component.ListProg
import Component.MiniProg
import Data.String
import SecondMinSpec
import Grisette
import Component.CEGISList
import Common.ListProg
import Common.T
import Component
import Test.QuickCheck
import Common.Timing



secondMinComponentListCAuxProg :: (Num a, Num b) => CListAuxProg a b
secondMinComponentListCAuxProg =
  CListAuxProg
    [ CMiniProg
      [ CNode (CMLSOpConst "min" 8) 1 [0]]
      1
    ]

secondMinComponentListCProg :: CListProg Integer Integer
secondMinComponentListCProg =
  CListProg
    secondMinComponentListCAuxProg
    ( CListCombProg
      ( CMiniProg
        [ CNode (CMLSOp "max") 3 [1, 2],
          CNode (CMLSOp "min") 4 [0, 3]
        ]
        4))

secondMinComponentListProgSpec :: (IsString a, Num a) => ListProgSpec a
secondMinComponentListProgSpec =
  ListProgSpec
    ( ListAuxProgSpec
        [ MiniProgSpec
          [ ComponentSpec (MLSOpConst "min" 8) 1
          ]
          1
          0
        ])
    ( ListCombProgSpec
        ( MiniProgSpec
            [ ComponentSpec (MLSOp "min") 2,
              ComponentSpec (MLSOp "max") 2
            ]
            3
            1))

secondMinComponentListProg :: forall a. (IsString a, Num a) => ListProg (SymIntN 5) a
secondMinComponentListProg = genSymSimple (secondMinComponentListProgSpec :: ListProgSpec a) "prog"

secondMinInputsGenRaw :: Enum s => (s, s) -> Gen [[s]]
secondMinInputsGenRaw e = do
  n <- getSize
  vectorOf 1 (vectorOf n $ chooseEnum e)

secondMinComponentListComb2ProgSpec :: (IsString a, Num a) => ListComb2ProgSpec a
secondMinComponentListComb2ProgSpec =
  ListComb2ProgSpec
  [ MiniProgSpec
    [ ComponentSpec (MLSOp "min") 2
    ]
    2
    0]

secondMinComponentListComb2Prog :: forall a. (IsString a, Num a) => ListComb2Prog (SymIntN 5) a
secondMinComponentListComb2Prog = genSymSimple (secondMinComponentListComb2ProgSpec :: ListComb2ProgSpec a) "prog"


componentListMain :: String -> IO ()
componentListMain _ = do
  let configb = precise z3 {Grisette.transcript = Just "b.smt2"}
  qcListProg1 1 17 8 2 4 (secondMinInf 9) secondMinComponentListCProg
  
  Right (_, prog@(CListProg aux comb) :: CListProg (IntN 5) (IntN 8)) <- timeItAll "CEGIS" $ cegisListQuickCheck1
    configb
    (restrictedSecondMinSpecCon 8)
    1
    1
    (secondMinInputsGenRaw (-8, 8))
    4
    (secondMinComponentListProg :: ListProg (SymIntN 5) (SymIntN 8))
  print prog

  Right (_, r :: CListComb2Prog (IntN 5) (IntN 8)) <- cegisListComb2QuickCheck
    configb
    aux
    1
    (secondMinInputsGenRaw (-8, 8))
    4
    (secondMinComponentListComb2Prog :: ListComb2Prog (SymIntN 5) (SymIntN 8))
    listAuxcfuncMap
    listCombfuncMap
    listCombcfuncMap
    (fresh ())
  
  qcListComb2AgainstListAux 17 8 4 aux r