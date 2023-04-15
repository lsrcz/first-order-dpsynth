module Component.CEGISListAux where

import Component.CEGISAux
import Common.Timing
import Common.Val
import Component.CEGIS (M, sbvCheckSatResult)
import Component.IntermediateVarSet
import Control.Monad.Except
import Control.Monad.Writer
import Data.Bifunctor
import Data.Maybe
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Grisette
import Grisette.Backend.SBV.Data.SMT.Lowering
import Test.QuickCheck
import Component.ListAuxProg
import Component.ListOps
import Common.ListProg
import Component.MiniProg
import Component.ConcreteMiniProg
import Debug.Trace

cegisListMiniQuickCheck ::
  forall n cval val a c.
  (ValLike val, Show cval, CValLike cval, ToCon a c, Show c, ToSym c a, Eq c, Integral c, EvaluateSym val,
  ToCon val cval, ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a, Read c, Show val) =>
  GrisetteSMTConfig n ->
  ([[c]] -> Either VerificationConditions c) ->
  Int ->
  Gen [[c]] ->
  Int ->
  MiniProg (MLOpCode a) val ->
  MLFuncMap a ->
  MLCFuncMap c ->
  (Int -> M (MListProgVal a)) ->
  IO (Either SolvingFailure ([[[c]]], CMiniProg (CMLOpCode c) cval))
cegisListMiniQuickCheck config spec numInputs inputGen maxGenSize prog funcMap cfuncMap gen = SBV.runSMTWith (sbvConfig config) {transcript = Just "guess.smt2"} $ do
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
          (miniProgWellFormedConstraints numInputs funcMap prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    f :: Int -> [[a]] -> (ExceptT VerificationConditions UnionM (MListProgVal a), IntermediateVarSet)
    f idx input = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT (interpretListMiniProg input prog funcMap gen) (FreshIdentWithInfo "x" idx)

    phiIO :: Int -> [[a]] -> a -> SymBool
    phiIO idx i o = simpleMerge $ do
      x <- runExceptT $ fst $ f idx i
      return $ x ==~ Right (mrgReturn $ LInt o)

    check :: Int -> Model -> IO (Either SolvingFailure ([[c]], Int, c))
    check i _ | i > maxGenSize = return (Left Unsat)
    check i candidate = do
      let evaluated :: CMiniProg (CMLOpCode c) cval = evaluateSymToCon candidate prog
      r <-
        quickCheckWithResult
          (stdArgs {maxSize = i, maxSuccess = 1000, chatty = False})
          ( forAll (resize i inputGen) $ \input ->
              let p = interpretCListMiniProgOnConInputs input evaluated cfuncMap :: Either VerificationConditions (CListProgVal c)
                  sp = spec input
               in case (p, sp) of
                    (Right v, Right sv) -> v == CLInt sv
                    _ -> error "Bad"
          )
      case r of
        Success {} -> check (i + 1) candidate
        Failure _ _ _ _ _ _ _ _ _ _ r _ _ -> do
          let input = read (head r) :: [[c]]
          -- let input = toSym $ unGen inputGen curSeed i
          case spec input of
            Right v -> return $ Right (input, i, v)
            Left AssumptionViolation -> check (i + 1) candidate
            Left AssertionViolation -> error "Should not happen"

{-
          return $ Right (input, i, ; _ -> error "Bad")
          -}
        _ -> error "???"

    guess :: Int -> [[c]] -> c -> SymBiMap -> SBVC.Query (SymBiMap, Either SolvingFailure Model)
    guess idx candidatei candidateo origm = do
      liftIO $ print candidatei
      liftIO $ print candidateo
      let SymBool evaluated = phiIO idx (toSym candidatei) (toSym candidateo)
      (newm, lowered) <- lowerSinglePrimCached config evaluated origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          liftIO $ print (evaluateSymToCon model prog :: CMiniProg (CMLOpCode c) cval)
          return (newm, Right model)
        _ -> return (newm, Left $ sbvCheckSatResult r)
    loop ::
      Int ->
      Either SolvingFailure Model ->
      Int ->
      -- [[[a]]] ->
      [[[c]]] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([[[c]]], CMiniProg (CMLOpCode c) cval))
    loop idx (Right mo) curSize cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check curSize mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (cex, nextSize, cexr) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex cexr origm
          loop (idx + 1) res nextSize (cex : cexs) newm
    loop _ (Left v) _ _ origm = return (origm, Left v)

cegisListAuxQuickCheck ::
  forall n cval val a c.
  ( ValLike val,
    Show cval,
    CValLike cval,
    ToCon a c,
    Show c,
    ToSym c a,
    Eq c,
    EvaluateSym val,
    ToCon val cval,
    ExtractSymbolics a,
    EvaluateSym a,
    Mergeable a,
    SEq a,
    Show a,
    ToSym a a,
    ToCon a a,
    Read c,
    Show val
  ) =>
  GrisetteSMTConfig n ->
  ([[c]] -> Either VerificationConditions c) ->
  Int ->
  Gen (DistinguishingInputs c) ->
  Int ->
  ListAuxProg val a ->
  MLFuncMap a ->
  MLCFuncMap c ->
  (Int -> M (MListProgVal a)) ->
  IO (Either SolvingFailure ([DistinguishingInputs c], CListAuxProg cval c))
cegisListAuxQuickCheck config spec numInputs inputGen maxGenSize prog funcMap cfuncMap gen = SBV.runSMTWith (sbvConfig config) {transcript = Just "guess.smt2"} $ do
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
      loop 1 mr 1 [] newm
  where
    -- forallSymbols :: SymbolSet
    -- forallSymbols = extractSymbolics inputs

    wellFormed :: SymBool
    wellFormed = simpleMerge $ do
      v <-
        runExceptT
          (listAuxProgWellFormedConstraints numInputs funcMap prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    f :: Int -> [[a]] -> (ExceptT VerificationConditions UnionM [a], IntermediateVarSet)
    f idx input = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT (interpretListAuxProg input prog funcMap gen) (FreshIdentWithInfo "x" idx)

    phiI :: Int -> [[a]] -> [[a]] -> SymBool
    phiI idx i1 i2 = simpleMerge $ do
      x1 <- runExceptT $ fst $ f (idx * 2) i1
      x2 <- runExceptT $ fst $ f (idx * 2 + 1) i2
      case (x1, x2) of
        (Right x1e, Right x2e) -> return $ x1e /=~ x2e
        _ -> con False

    check :: Int -> Model -> IO (Either SolvingFailure (DistinguishingInputs c, Int))
    check i _ | i > maxGenSize = return (Left Unsat)
    check i candidate = do
      let evaluated :: CListAuxProg cval c = evaluateSymToCon candidate prog
      liftIO $ print evaluated
      r <-
        quickCheckWithResult
          (stdArgs {maxSize = i, maxSuccess = 10000, chatty = False})
          ( forAll (resize i inputGen) $ \(DistinguishingInputs i1 i2 v) ->
              let i1v = zipWith (\l r -> l ++ [r]) i1 v
                  i2v = zipWith (\l r -> l ++ [r]) i2 v
                  p1 = interpretCListAuxProgOnConInputs i1 evaluated cfuncMap :: Either VerificationConditions [c]
                  sp1 = spec i1v
                  sp1' = spec i1
                  p2 = interpretCListAuxProgOnConInputs i2 evaluated cfuncMap :: Either VerificationConditions [c]
                  sp2 = spec i2v
                  sp2' = spec i2
               in 
                  case (p1, sp1, sp1', p2, sp2, sp2') of
                    ( Right v1,
                      Right sv1,
                      Right sv1',
                      Right v2,
                      Right sv2,
                      Right sv2'
                      ) ->
                        let cv1 = v1 :: [c]
                            cv2 = v2 :: [c]
                            csv1 = sv1 :: c
                            csv2 = sv2 :: c
                            csv1' = sv1' :: c
                            csv2' = sv2' :: c
                         in csv1 == csv2 || cv1 /= cv2 || csv1' /= csv2'
                    _ -> error "Bad"
          )
      case r of
        Success {} -> check (i + 1) candidate
        Failure _ _ _ _ _ _ _ _ _ _ cex _ _ -> do
          let input :: DistinguishingInputs c = read (head cex) -- unGen inputGen curSeed i
          {-liftIO $ print input
          liftIO $ print i
          liftIO $ print r-}
          return $ Right (input, i)
        {-
        case spec input of
          ExceptT (SingleU (Right v)) -> return $ Right (input, i, v)
          ExceptT (SingleU (Left AssumptionViolation)) -> check (i + 1) candidate
          -}

        {-
                  return $ Right (input, i, ; _ -> error "Bad")
                  -}
        _ -> error "???"

    guess :: Int -> DistinguishingInputs c -> SymBiMap -> SBVC.Query (SymBiMap, Either SolvingFailure Model)
    guess idx d@(DistinguishingInputs i1 i2 _) origm = do
      liftIO $ print d
      let SymBool evaluated = phiI idx (toSym i1) (toSym i2)
      (newm, lowered) <- lowerSinglePrimCached config evaluated origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          {-let ep = evaluateSymToCon model prog :: CListAuxProg cval c
          let r1 = runFreshT (interpretCListAuxProgOnSymInputs (toSym i1) ep funcMap) $$(nameWithLoc "r1") :: ExceptT VerificationConditions UnionM [a]
          let r2 = runFreshT (interpretCListAuxProgOnSymInputs (toSym i2) ep funcMap) $$(nameWithLoc "r2") :: ExceptT VerificationConditions UnionM [a]
          liftIO $ print ep
          liftIO $ print i1
          liftIO $ print i2
          liftIO $ print r1
          liftIO $ print r2-}
          return (newm, Right model)
        _ -> return (newm, Left $ sbvCheckSatResult r)

    loop ::
      Int ->
      Either SolvingFailure Model ->
      Int ->
      -- [[[a]]] ->
      [DistinguishingInputs c] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([DistinguishingInputs c], CListAuxProg cval c))
    loop idx (Right mo) curSize cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check curSize mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (cex, nextSize) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex origm
          loop (idx + 1) res nextSize (cex : cexs) newm
    loop _ (Left v) _ _ origm = return (origm, Left v)