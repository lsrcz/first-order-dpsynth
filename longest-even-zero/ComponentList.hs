module ComponentList where

lezComponentListCAuxProg :: (Num a, Num b) => CListAuxProg a b
lezComponentListCAuxProg =
  CListAuxProg
    [ CMiniProg
      [ CNode (CMLSOpConst "scanrCommLinear" 1) 1 [0], -- min
        CNode (CMLSOpConst "scanrCommLinear" 2) 2 [0], -- max
        CNode (CMLSOpConst "zipMinus") 3 [1, 2],
        CNode (CMLSOpConst "offset" (1)) 4 [3],
        CNode (CMLSOpConst "filter" 0) 5 [4],
        CNode (CMLSOpConst "scanrCommLinear" 0) 6 [5],
        CNode (CMLSOp "head") 7 [6]
      ]
      4
    ] -- min

componentListMain :: String -> IO ()
componentListMain _ = do
  print $ interpretCListAuxProgOnConInputs [[1,2,0,0,3,0,0]] (lezComponentListCAuxProg :: CListAuxProg Integer Integer)
    listAuxcfuncMap 