module Main where
import Component.ListAuxProg
import Component.ListOps
import Component.ConcreteMiniProg
import Component.MiniProg
import Grisette
import Component.CEGISListAux
import Test.QuickCheck
import Common.ListProg
import Data.String

evencountComponentListAuxCProg :: CListAuxProg Integer Integer
evencountComponentListAuxCProg =
  CListAuxProg
  [CMiniProg
   [CNode (CMLSOpConst "count" 2) 1 [0]]
   1]

evencountComponentListMiniProgSpec :: (IsString a, Num a) => MiniProgSpec (MLOpCode a)
evencountComponentListMiniProgSpec =
  MiniProgSpec
   [ComponentSpec (MLSOpConst "count" "a") 1]
   1
   0

evencountComponentListAuxProg :: forall a. (IsString a, Num a) => MiniProg (MLOpCode a) (SymIntN 5)
evencountComponentListAuxProg = genSymSimple (evencountComponentListMiniProgSpec :: MiniProgSpec (MLOpCode a)) "prog"

evencountSpecCon :: forall c. (Integral c, Show c, Num c, Ord c) => [[c]] -> Either VerificationConditions c
evencountSpecCon l = do
  return $ go (head l)
  where
    go [] = 0
    go (x:xs) | even x = 1 + go xs
    go (_:xs) = go xs

evenListAuxInputsGen :: Enum s => (s, s) -> Gen [[s]]
evenListAuxInputsGen e = do
  n <- getSize
  vectorOf 1 (vectorOf n $ chooseEnum e)

evenListIntermediateGen :: (GenSymSimple () a, MonadFresh m, Num a, Mergeable a) => Int -> m (MListProgVal a)
evenListIntermediateGen len = do
  b <- simpleFresh ()
  i <- simpleFresh ()
  il <- simpleFresh (SimpleListSpec len ())
  chooseFresh [LBool b, LInt i, LIntList il]

main :: IO ()
main = do
  let configb = precise boolector {Grisette.transcript = Just "b.smt2"}
  Right (_, x :: CMiniProg (CMLOpCode (IntN 8)) (IntN 5) ) <- cegisListMiniQuickCheck
    configb
    evencountSpecCon
    1
    (evenListAuxInputsGen (-8, 8))
    4
    (evencountComponentListAuxProg :: MiniProg (MLOpCode (SymIntN 8)) (SymIntN 5))
    listAuxfuncMap
    listAuxcfuncMap
    evenListIntermediateGen
  print x
