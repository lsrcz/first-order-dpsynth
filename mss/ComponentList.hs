module ComponentList where

import Component.ConcreteMiniProg
import Component.ListAuxProg
import Component.ListCombProg
import Component.ListOps
import Component.ListProg
import Component.ListQuickCheck
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

mssComponentListCProg :: CListProg Integer Integer
mssComponentListCProg =
  CListProg
    ( CListAuxProg
        [ CMiniProg
            [ CNode (CMLSOpConst "scanrCommLinear" 0) 1 [0],
              CNode (CMLSOp "max") 2 [1],
              CNode (CMLSOpConst "intConst" 0) 3 [],
              CNode (CMLSOpConst "binCommLinear" 2) 4 [2, 3]
            ]
            4
        ]
    )
    ( CListCombProg
        ( CMiniProg
            [ CNode (CMLSOp "binPlus") 3 [1, 2],
              CNode (CMLSOp "max") 4 [0, 3]
            ]
            4
        )
    )

mssComponentListProgSpec :: (IsString a, Num a) => ListProgSpec a
mssComponentListProgSpec =
  ListProgSpec
    ( ListAuxProgSpec
        [ MiniProgSpec
            [ ComponentSpec (MLSOpConst "scanrCommLinear" "y1") 1,
              ComponentSpec (MLSOpConst "scanlCommLinear" "y2") 1,
              ComponentSpec (MLSOp "max") 1,
              ComponentSpec (MLSOp "min") 1,
              ComponentSpec (MLSOpConst "intConst" 0) 0,
              ComponentSpec (MLSOpConst "binCommLinear" "y3") 2,
              ComponentSpec (MLSOpConst "binCommLinear" "y4") 2
            ]
            1
            3
        ]
    )
    ( ListCombProgSpec
        ( MiniProgSpec
            [ ComponentSpec (MLSOp "binPlus") 2,
              ComponentSpec (MLSOp "binMinus") 2,
              ComponentSpec (MLSOp "max") 2,
              ComponentSpec (MLSOp "min") 2
            ]
            3
            1
        )
    )

mssComponentListProg :: forall a. (IsString a, Num a) => ListProg (SymIntN 5) a
mssComponentListProg = genSymSimple (mssComponentListProgSpec :: ListProgSpec a) "prog"

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
  print $ interpretCListProgOnConInputs [[1, 3, -2, -3, 5, 7, -1, -8, 4, 6]] 12 mssComponentListCProg listAuxcfuncMap listCombcfuncMap
  qcListProg1 17 8 4 mssAlgo mssComponentListCProg

  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}

  Right (_, r :: CListProg (IntN 5) (IntN 8)) <- timeItAll "CEGIS" $ cegisListQuickCheck1
    configb
    restrictedMssSpecCon
    1
    (mssInputsGen (-8, 8))
    4
    (mssComponentListProg :: ListProg (SymIntN 5) (SymIntN 8))
  print r

  qcListProg1 17 8 4 mssAlgo r


