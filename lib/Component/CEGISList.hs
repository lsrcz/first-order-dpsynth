module Component.CEGISList where

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
import Common.T


cegisListQuickCheck ::
  forall n cval val a c.
  (ValLike val, Show cval, CValLike cval, ToCon a c, Show c, ToSym c a, Eq c, Integral c, EvaluateSym val,
  ToCon val cval, ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a, Read c, Show val) =>
  GrisetteSMTConfig n ->
  ([[c]] -> Either VerificationConditions c) ->
  Int ->
  Gen [[c]] ->
  Int ->
  ListProg val a ->
  MLFuncMap a ->
  MLCFuncMap c ->
  MLCombFuncMap a ->
  MLCombCFuncMap c ->
  (Int -> M (MListProgVal a)) ->
  M (MT a) ->
  IO (Either SolvingFailure ([[[c]]], CListProg cval c))
cegisListQuickCheck config spec numInputs inputGen maxGenSize prog funcMap cfuncMap combFuncMap ccombFuncMap gen combGen = SBV.runSMTWith (sbvConfig config) {transcript = Just "guess.smt2"} $ do
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
    -- forallSymbols :: SymbolSet
    -- forallSymbols = extractSymbolics inputs

    wellFormed :: SymBool
    wellFormed = simpleMerge $ do
      v <-
        runExceptT
          (listProgWellFormedConstraints numInputs funcMap combFuncMap prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    f :: Int -> [[a]] -> a -> (ExceptT VerificationConditions UnionM a, IntermediateVarSet)
    f idx input prevRes = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $
      runExceptT $ runFreshT (interpretListProg input prevRes prog funcMap combFuncMap gen combGen) (FreshIdentWithInfo "x" idx)

    phiIO :: Int -> [[a]] -> a -> a -> SymBool
    phiIO idx i prevo o = simpleMerge $ do
      x <- runExceptT $ fst $ f idx i prevo
      return $ x ==~ Right o

    check :: Int -> Model -> IO (Either SolvingFailure ([[c]], Int, c, c))
    check i _ | i > maxGenSize = return (Left Unsat)
    check i candidate = do
      let evaluated :: CListProg cval c = evaluateSymToCon candidate prog
      r <-
        quickCheckWithResult
          (stdArgs {maxSize = i, maxSuccess = 1000, chatty = False})
          ( forAll (resize i inputGen) $ \input ->
              let prevp = case spec (fmap init input) of Right v -> v; _ -> error "Bad"
                  p = interpretCListProgOnConInputs input prevp evaluated cfuncMap ccombFuncMap :: Either VerificationConditions c
                  sp = spec input
               in case (p, sp) of
                    (Right v, Right sv) -> v == sv
                    _ -> error "Bad"
          )
      case r of
        Success {} -> check (i + 1) candidate
        Failure _ _ _ _ _ _ _ _ _ _ res _ _ -> do
          let input = read (head res) :: [[c]]
          -- let input = toSym $ unGen inputGen curSeed i
          case (spec (fmap init input), spec input) of
            (Right prevv, Right v) -> return $ Right (input, i, prevv, v)
            (_, Left AssumptionViolation) -> check (i + 1) candidate
            (Left AssumptionViolation, _) -> check (i + 1) candidate
            _ -> error "Should not happen"

{-
          return $ Right (input, i, ; _ -> error "Bad")
          -}
        _ -> error "???"

    guess :: Int -> [[c]] -> c -> c -> SymBiMap -> SBVC.Query (SymBiMap, Either SolvingFailure Model)
    guess idx candidatei candidateprevo candidateo origm = do
      liftIO $ print candidatei
      liftIO $ print candidateprevo
      liftIO $ print candidateo
      let e@(SymBool evaluated) = phiIO idx (toSym candidatei) (toSym candidateprevo) (toSym candidateo)
      (newm, lowered) <- lowerSinglePrimCached config evaluated origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          liftIO $ print (evaluateSymToCon model prog :: CListProg cval c)
          liftIO $ print (evaluateSym False model e)
          liftIO $ print (interpretCListProgOnConInputs candidatei candidateprevo (evaluateSymToCon model prog :: CListProg cval c) listAuxcfuncMap listCombcfuncMap)
          return (newm, Right model)
        _ -> return (newm, Left $ sbvCheckSatResult r)
    loop ::
      Int ->
      Either SolvingFailure Model ->
      Int ->
      -- [[[a]]] ->
      [[[c]]] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([[[c]]], CListProg cval c))
    loop idx (Right mo) curSize cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check curSize mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (cex, nextSize, cexprevr, cexr) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex cexprevr cexr origm
          loop (idx + 1) res nextSize (cex : cexs) newm
    loop _ (Left v) _ _ origm = return (origm, Left v)
  

cegisListQuickCheck1 ::
  forall n cval val a c.
  (ValLike val, Show cval, CValLike cval, ToCon a c, Show c, ToSym c a, Eq c, Integral c, EvaluateSym val,
  ToCon val cval, ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a, Read c, Show val,
  GenSym ExactSize (ListProgVal a), Num a, SOrd a, SimpleMergeable a, GenSymSimple () a) =>
  GrisetteSMTConfig n ->
  ([[c]] -> Either VerificationConditions c) ->
  Int ->
  Gen [[c]] ->
  Int ->
  ListProg val a ->
  {-MLFuncMap a ->
  MLCFuncMap c ->
  MLCombFuncMap a ->
  MLCombCFuncMap c ->
  (Int -> M (MListProgVal a)) ->
  M (MT a) ->-}
  IO (Either SolvingFailure ([[[c]]], CListProg cval c))
cegisListQuickCheck1 config spec numInputs inputGen maxGenSize prog =
  cegisListQuickCheck config spec numInputs inputGen maxGenSize prog
    listAuxfuncMap listAuxcfuncMap listCombfuncMap listCombcfuncMap (fresh . ExactSize) (fresh ())