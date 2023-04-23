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
import ComponentAux
import Test.QuickCheck
import Common.Timing



secondMinComponentListCAuxProg :: (Num a, Num b) => CListAuxProg a b
secondMinComponentListCAuxProg =
  CListAuxProg
    [ CMiniProg
      [ CNode (CMLSOp "min") 1 [0]]
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

componentListMain :: String -> IO ()
componentListMain _ =
  qcListProg1 1 17 8 2 4 (secondMinInf 9) secondMinComponentListCProg
