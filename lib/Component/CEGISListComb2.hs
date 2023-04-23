module Component.CEGISListComb2 where

import Common.Timing
import Common.Val
import Component.CEGIS (M, sbvCheckSatResult)
import Component.IntermediateVarSet
import Control.Monad.Except
import Control.Monad.Writer
import Data.Bifunctor
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Grisette
import Grisette.Backend.SBV.Data.SMT.Lowering
import Test.QuickCheck
import Component.ListOps
import Common.ListProg
import Component.ListProg
import Component.ListAuxProg
import Component.ListComb2Prog
import Common.T
import Data.Either

data ListComb2CounterExample c =
  ListComb2CounterExample { lc2Whole :: [[c]], lc2Inputs :: [c], lc2Intermediates :: [c], lc2Result :: [c] }

cegisListComb2QuickCheck ::
  forall n cval val a c.
  (ValLike val, Show cval, CValLike cval, ToCon a c, Show c, ToSym c a, Eq c, Integral c, EvaluateSym val,
  ToCon val cval, ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a, Read c, Show val) =>
  GrisetteSMTConfig n ->
  CListAuxProg cval c ->
  Int ->
  Gen [[c]] ->
  Int ->
  ListComb2Prog val a ->
  MLCFuncMap c ->
  MLCombFuncMap a ->
  MLCombCFuncMap c ->
  M (MT a) ->
  IO (Either SolvingFailure ([ListComb2CounterExample c], CListComb2Prog cval c))
cegisListComb2QuickCheck config spec@(CListAuxProg progs) numInputs inputGen maxGenSize prog cfuncMap combFuncMap ccombFuncMap combGen =
  SBV.runSMTWith (sbvConfig config) $ do
    let SymBool t = wellFormed
    (newm, a) <- lowerSinglePrim config t
    SBVC.query $
      snd <$> do
        SBV.constrain a
        r <- timeItAll "INITIAL GUESS" SBVC.checkSat
        mr <- case r of
          SBVC.Sat -> do
            md <- SBVC.getModel
            return $ Right $ parseModel config md newm
          _ -> return $ Left $ sbvCheckSatResult r
        loop 1 mr 2 [] newm
  where
    numComb2Inputs = numInputs + length progs
    wellFormed :: SymBool
    wellFormed = simpleMerge $ do
      v <-
        runExceptT
          (listComb2ProgWellFormedConstraints numComb2Inputs combFuncMap prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True
    f :: Int -> [a] -> [a] -> (ExceptT VerificationConditions UnionM [a], IntermediateVarSet)
    f idx input intermediates = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $
      runExceptT $ runFreshT (interpretListComb2Prog input intermediates prog combFuncMap combGen) (FreshIdentWithInfo "x" idx)
    phiIO :: Int -> [a] -> [a] -> [a] -> SymBool
    phiIO idx i intermediates o = simpleMerge $ do
      x <- runExceptT $ fst $ f idx i intermediates 
      return $ x ==~ Right o

    check :: Int -> Model -> IO (Either SolvingFailure (Int, ListComb2CounterExample c))
    check i _ | i > maxGenSize = return (Left Unsat)
    check i candidate = do
      let evaluated :: CListComb2Prog cval c = evaluateSymToCon candidate prog
      r <- quickCheckWithResult
        (stdArgs {maxSize = i, maxSuccess = 1000, chatty = False})
        ( forAll (resize i inputGen) $ \input ->
            let
                pinput = fmap init input
                linput = fmap last input
                r1 = interpretCListAuxProgOnConInputs pinput spec cfuncMap
                r2 = interpretCListAuxProgOnConInputs input spec cfuncMap
              in case (r1, r2) of
                  (Right vr1, Right vr2) ->
                    interpretCListComb2ProgOnConInputs linput vr1 evaluated ccombFuncMap == Right vr2
                  _ -> error "Bad"
            )
      case r of
        Success {} -> check (i + 1) candidate
        Failure _ _ _ _ _ _ _ _ _ _ res _ _ -> do
          let input = read (head res) :: [[c]]
          let pinput = fmap init input
          let linput = fmap last input
          let r1 = interpretCListAuxProgOnConInputs pinput spec cfuncMap
          let r2 = interpretCListAuxProgOnConInputs input spec cfuncMap
          case (r1, r2) of
            (Right vr1, Right vr2) -> return $ Right (i, ListComb2CounterExample input linput vr1 vr2)
            _ -> error "Should not happen"
        _ -> error "???"
    guess :: Int -> ListComb2CounterExample c -> SymBiMap -> SBVC.Query (SymBiMap, Either SolvingFailure Model)
    guess idx (ListComb2CounterExample _ i intermediate r) origm = do
      liftIO $ print i
      liftIO $ print intermediate
      liftIO $ print r
      let e@(SymBool evaluated) = phiIO idx (toSym i) (toSym intermediate) (toSym r)
      (newm, lowered) <- lowerSinglePrimCached config evaluated origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          liftIO $ print (evaluateSymToCon model prog :: CListComb2Prog cval c)
          liftIO $ print (interpretCListComb2ProgOnConInputs i intermediate (evaluateSymToCon model prog :: CListComb2Prog cval c) ccombFuncMap)
          return (newm, Right model)
        _ -> return (newm, Left $ sbvCheckSatResult r)

    loop ::
      Int ->
      Either SolvingFailure Model ->
      Int ->
      [ListComb2CounterExample c] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([ListComb2CounterExample c], CListComb2Prog cval c))
    loop idx (Right mo) curSize cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check curSize mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (nextSize, cex) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex origm
          loop (idx + 1) res nextSize (cex : cexs) newm
    loop _ (Left v) _ _ origm = return (origm, Left v)
          





