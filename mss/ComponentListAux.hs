module ComponentListAux where
import Component.ListAuxProg
import Component.ConcreteMiniProg
import Component.ListOps
import Component.MiniProg
import Common.ListProg
import Grisette
import Component.CEGISAux 
import Test.QuickCheck
import Component.CEGISListAux (cegisListAuxQuickCheck, cegisListMiniQuickCheck)
import Component
import Control.Monad.Except
import Component.Ops
import Data.String
import Data.Foldable

mssComponentListAuxCProg :: CListAuxProg Integer Integer
mssComponentListAuxCProg =
  CListAuxProg
  [CMiniProg
   [CNode (CMLSOpConst "scanlCommLinear" 0) 1 [0],
    CNode (CMLSOp "max") 2 [1],
    CNode (CMLSOpConst "intConst" 0) 3 [],
    CNode (CMLSOpConst "binCommLinear" 2) 4 [2,3]]
   4,
   CMiniProg
   [CNode (CMLSOpConst "scanrCommLinear" 0) 1 [0],
    CNode (CMLSOp "max") 2 [1],
    CNode (CMLSOpConst "intConst" 0) 3 [],
    CNode (CMLSOpConst "binCommLinear" 2) 4 [2,3]]
   4
   ]

mssComponentListAuxProgSpec :: (IsString a, Num a) => ListAuxProgSpec a
mssComponentListAuxProgSpec =
  ListAuxProgSpec
  [{-MiniProgSpec
    [ComponentSpec (MLSOpConst "scanlCommLinear" "x1") 1,
     ComponentSpec (MLSOp "max") 1,
     ComponentSpec (MLSOpConst "intConst" 0) 0,
     ComponentSpec (MLSOpConst "binCommLinear" "x3") 2
     ]
    1
    3,-}
   MiniProgSpec
    [ComponentSpec (MLSOpConst "scanrCommLinear" "y1") 1,
     ComponentSpec (MLSOpConst "scanlCommLinear" "y2") 1,
     ComponentSpec (MLSOp "max") 1,
     ComponentSpec (MLSOp "min") 1,
     ComponentSpec (MLSOpConst "intConst" 0) 0,
     ComponentSpec (MLSOpConst "binCommLinear" "y3") 2,
     ComponentSpec (MLSOpConst "binCommLinear" "y4") 2
     ]
    1
    3]

mssComponentListAuxProg :: forall a. (IsString a, Num a) => ListAuxProg (SymIntN 5) a
mssComponentListAuxProg = genSymSimple (mssComponentListAuxProgSpec :: ListAuxProgSpec a) "prog"

mpsSpec :: Num a => MiniProgSpec (MLOpCode a)
mpsSpec = MiniProgSpec
    [ComponentSpec (MLSOpConst "scanlCommLinear" 0) 1,
     ComponentSpec (MLSOp "max") 1,
     ComponentSpec (MLSOpConst "intConst" 0) 0,
     ComponentSpec (MLSOpConst "binCommLinear" 2) 2
     ]
    1
    3

mpsComponentListMiniProg :: forall a. (Num a) => MiniProg (MLOpCode a) (SymIntN 5)
mpsComponentListMiniProg = genSymSimple (mpsSpec :: MiniProgSpec (MLOpCode a)) "prog"

mssListIntermediateGen :: (GenSymSimple () a, MonadFresh m, Num a, Mergeable a) => Int -> m (MListProgVal a)
mssListIntermediateGen len = do
  b <- simpleFresh ()
  i <- simpleFresh ()
  il <- simpleFresh (SimpleListSpec len ())
  chooseFresh [LBool b, LInt i, LIntList il]

mssListAuxInputsGen :: Enum s => (s, s) -> Gen [[s]]
mssListAuxInputsGen e = do
  n <- getSize
  vectorOf 1 (vectorOf n $ chooseEnum e)

mssListAuxDInputsGen :: Enum s => (s, s) -> Gen (DistinguishingInputs s)
mssListAuxDInputsGen e = do
  n <- getSize
  i1 <- vectorOf 1 (vectorOf n $ chooseEnum e)
  i2 <- vectorOf 1 (vectorOf n $ chooseEnum e)
  v <- vectorOf 1 $ chooseEnum e
  return $ DistinguishingInputs i1 i2 v

restrictedMpsSpec ::
  forall a e.
  (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  [[a]] ->
  ExceptT VerificationConditions UnionM a
restrictedMpsSpec l = do
  mrgTraverse_ (\x -> symAssume $ x >=~ -8 &&~ x <=~ 8) $ join l
  go (head l) 0 0
  where
    go [] _ cur = mrgReturn cur
    go (x:xs) acc cur = go xs (acc + x) (symMax (acc + x) cur)

restrictedMpsSpecCon ::
  forall c.
  (Show c, Num c, Ord c) =>
  [[c]] ->
  Either VerificationConditions c 
restrictedMpsSpecCon l = do
  traverse_ (\x -> when (x < -8 &&~ x > 8) $ throwError AssertionViolation) $ join l
  go (head l) 0 0
  where
    go [] _ cur = return cur
    go (x:xs) acc cur = go xs (acc + x) (max (acc + x) cur)

componentListAuxMain :: String -> IO ()
componentListAuxMain _ = do
  print $ interpretCListAuxProgOnConInputs [[1,3,-2,-3,5,7,-1,-8,4,3]] mssComponentListAuxCProg listAuxcfuncMap
  print $ interpretCListAuxProgOnConInputs [[-1,-2,2]] mssComponentListAuxCProg listAuxcfuncMap


  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}
  print $ restrictedMpsSpec [[1 :: SymInteger ,3,-3,5]]

  Right (_, r :: CMiniProg (CMLOpCode (IntN 8)) (IntN 5)) <- cegisListMiniQuickCheck
    configb
    restrictedMpsSpecCon
    1
    (mssListAuxInputsGen (-8 , 8))
    4
    (mpsComponentListMiniProg :: MiniProg (MLOpCode (SymIntN 8)) (SymIntN 5))
    listAuxfuncMap
    listAuxcfuncMap
    mssListIntermediateGen
  print r

    

  Right (_, r :: CListAuxProg (IntN 5) (IntN 8)) <- cegisListAuxQuickCheck
    configb
    restrictedMssSpecCon
    1
    (mssListAuxDInputsGen (-8 , 8))
    4
    (mssComponentListAuxProg :: ListAuxProg (SymIntN 5) (SymIntN 8))
    listAuxfuncMap
    listAuxcfuncMap
    mssListIntermediateGen
  print r
