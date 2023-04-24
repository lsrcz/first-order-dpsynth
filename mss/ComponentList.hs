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
import MSSSpec (mssAlgo)
import Grisette
import Component.CEGISList
import Common.ListProg
import Common.T
import Component
import ComponentAux
import Test.QuickCheck
import Common.Timing


mssComponentListCAuxProg :: (Num a, Num b) => CListAuxProg a b
mssComponentListCAuxProg =
  CListAuxProg
    [ CMiniProg
        [ CNode (CMLSOpConst "scanrCommLinear" 0) 1 [0],
          CNode (CMLSOpConst "max" $ -8) 2 [1],
          CNode (CMLSOpConst "intConst" 0) 3 [],
          CNode (CMLSOpConst "binCommLinear" 2) 4 [2, 3]
        ]
        4
    ]

mssComponentListCComb2Prog :: CListComb2Prog Integer Integer
mssComponentListCComb2Prog =
  CListComb2Prog
    [ CMiniProg
        [CNode (CMLSOpConst "intConst" 0) 2 [],
         CNode (CMLSOp "binPlus") 3 [0, 1],
         CNode (CMLSOp "max") 4 [2, 3]
        ]
        4
    ]

mssComponentListCProg :: CListProg Integer Integer
mssComponentListCProg =
  CListProg
    mssComponentListCAuxProg
    ( CListCombProg
        ( CMiniProg
            [ CNode (CMLSOp "binPlus") 3 [1, 2],
              -- CNode (CMLSOp "max") 4 [0, 3]
              CNode (CMLSOp "leq") 4 [0, 3],
              CNode (CMLSOp "ite") 5 [4, 3, 0]
            ]
            5
        )
    )

mssComponentListProgSpec :: (IsString a, Num a) => ListProgSpec a
mssComponentListProgSpec =
  ListProgSpec
    ( ListAuxProgSpec
        [ MiniProgSpec
            [ ComponentSpec (MLSOpConst "scanrCommLinear" "y1") 1,
              -- ComponentSpec (MLSOpConst "scanlCommLinear" "y2") 1,
              ComponentSpec (MLSOpConst "max" $ -8) 1,
              -- ComponentSpec (MLSOpConst "min" $ -8) 1,
              ComponentSpec (MLSOpConst "intConst" 0) 0,
              -- ComponentSpec (MLSOpConst "binCommLinear" "y3") 2,
              ComponentSpec (MLSOpConst "binCommLinear" "y4") 2
            ]
            1
            3
        ]
    )
    ( ListCombProgSpec
        ( MiniProgSpec
            [ ComponentSpec (MLSOp "binPlus") 2,
              -- ComponentSpec (MLSOp "binMinus") 2,
              ComponentSpec (MLSOp "leq") 2,
              ComponentSpec (MLSOp "ite") 3
              --ComponentSpec (MLSOp "max") 2,
              --ComponentSpec (MLSOp "min") 2
            ]
            3
            2
        )
    )

mssComponentListProg :: forall a. (IsString a, Num a) => ListProg (SymIntN 5) a
mssComponentListProg = genSymSimple (mssComponentListProgSpec :: ListProgSpec a) "prog"


mssComponentListComb2ProgSpec :: (IsString a, Num a) => ListComb2ProgSpec a
mssComponentListComb2ProgSpec =
  ListComb2ProgSpec
  [ MiniProgSpec
    [ ComponentSpec (MLSOpConst "intConst" 0) 0,
      ComponentSpec (MLSOp "binPlus") 2,
      ComponentSpec (MLSOp "leq") 2,
      ComponentSpec (MLSOp "ite") 3
    ]
    2
    3]


mssComponentListComb2Prog :: forall a. (IsString a, Num a) => ListComb2Prog (SymIntN 5) a
mssComponentListComb2Prog = genSymSimple (mssComponentListComb2ProgSpec :: ListComb2ProgSpec a) "prog"

mssListIntermediateGen :: (GenSymSimple () a, MonadFresh m, Num a, Mergeable a) => Int -> m (MListProgVal a)
mssListIntermediateGen len = do
  b <- simpleFresh ()
  i <- simpleFresh ()
  il <- simpleFresh (SimpleListSpec len ())
  chooseFresh [LBool b, LInt i, LIntList il]

mssTIntermediateGen :: (GenSymSimple () a, MonadFresh m, Num a, Mergeable a) => m (MT a)
mssTIntermediateGen = do
  b <- simpleFresh ()
  i <- simpleFresh ()
  chooseFresh [TBool b, TInt i]

mssInputsGen :: Enum s => (s, s) -> Gen [[s]]
mssInputsGen e = do
  n <- getSize
  vectorOf 1 (vectorOf n $ chooseEnum e)

componentListMain :: String -> IO ()
componentListMain _ = do
  let configb = precise z3 {Grisette.transcript = Just "b.smt2"}
  qcListProg1 1 17 8 0 4 mssAlgo mssComponentListCProg
  --print $ interpretCListProgOnConInputs [[1, 3, -2, -3, 5, 7, -1, -8, 4, 6]] [12] mssComponentListCProg listAuxcfuncMap listCombcfuncMap
  --qcListComb2AgainstListAux 17 8 4 mssComponentListCAuxProg mssComponentListCComb2Prog


  Right (_, prog@(CListProg aux comb) :: CListProg (IntN 5) (IntN 8)) <- timeItAll "CEGIS" $ cegisListQuickCheck1
    configb
    restrictedMssSpecCon
    1
    1
    (mssInputsGen (-8, 8))
    4
    (mssComponentListProg :: ListProg (SymIntN 5) (SymIntN 8))
  print prog

  qcListProg1 1 17 8 0 4 mssAlgo prog

  Right (_, r :: CListComb2Prog (IntN 5) (IntN 8)) <- cegisListComb2QuickCheck
    configb
    aux
    1
    (mssInputsGen (-8, 8))
    4
    (mssComponentListComb2Prog :: ListComb2Prog (SymIntN 5) (SymIntN 8))
    listAuxcfuncMap
    listCombfuncMap
    listCombcfuncMap
    (fresh ())
  
  qcListComb2AgainstListAux 17 8 4 aux r