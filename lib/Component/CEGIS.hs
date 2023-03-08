module Component.CEGIS where

import Component.ConcreteMiniProg
import Component.ConcreteProg
import Component.IntermediateVarSet
import Component.MiniProg
import Component.Prog
import Control.Monad.Except
import Control.Monad.Writer
import Data.Bifunctor
import Data.Either
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Grisette
import Grisette.Backend.SBV.Data.SMT.Lowering

sbvCheckSatResult :: SBVC.CheckSatResult -> SolvingFailure
sbvCheckSatResult SBVC.Sat = error "Should not happen"
sbvCheckSatResult (SBVC.DSat msg) = DSat msg
sbvCheckSatResult SBVC.Unsat = Unsat
sbvCheckSatResult SBVC.Unk = Unk

type M a = FreshT (ExceptT VerificationConditions (WriterT IntermediateVarSet UnionM)) a

cegisCustomized' ::
  forall n a.
  (ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a) =>
  GrisetteSMTConfig n ->
  ([[a]] -> ExceptT VerificationConditions UnionM a) ->
  [[a]] ->
  Prog a ->
  FuncMap a ->
  M a ->
  IO (Either SolvingFailure ([[[a]]], Model))
cegisCustomized' config spec inputs prog funcMap gen = SBV.runSMTWith ((sbvConfig config) {SBV.transcript = Just "x.smt2"}) $ do
  let SymBool t = phiRight &&~ wellFormed
  (newm, a) <- lowerSinglePrim config t
  SBVC.query $
    snd <$> do
      SBV.constrain a
      r <- SBVC.checkSat
      mr <- case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          return $ Right $ parseModel config md newm
        _ -> return $ Left $ sbvCheckSatResult r
      loop (exceptFor exceptSymbols <$> mr) [] newm
  where
    forallSymbols :: SymbolSet
    forallSymbols = extractSymbolics inputs

    wellFormed :: SymBool
    wellFormed = simpleMerge $ do
      v <-
        runExceptT
          (progWellFormedConstraints prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    i :: M a
    i = interpretProg inputs prog funcMap gen
    i1 :: (UnionM (Either VerificationConditions a), IntermediateVarSet)
    i1 = simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT i "ep"
    {-
    i1r1 :: ExceptT VerificationConditions UnionM ()
    i1r1 = do
      x <- ExceptT $ fst i1
      -- symAssert $ spec x
      mrgReturn ()
      -}
    i1i :: IntermediateVarSet
    i1i = snd i1

    rm :: Model -> a -> SymBool
    rm m v = simpleMerge $ do
      r <- e
      return $ r ==~ Right v
      where
        e = evaluateSym False m $ fst i1

    exceptSymbols :: SymbolSet
    exceptSymbols = extractSymbolics inputs <> case i1i of IntermediateVarSet v -> v

    phiRight = simpleMerge $ do
      v <- fst i1
      con $ isRight v

    check :: Model -> IO (Either SolvingFailure ([[a]], a, Model))
    check candidate = do
      let evaluated :: CProg a = evaluateSymToCon candidate prog
      let evr :: ExceptT VerificationConditions UnionM a = interpretCProg inputs evaluated funcMap
      let spr :: ExceptT VerificationConditions UnionM a = spec inputs

      let negphi = simpleMerge $ do
            r <- runExceptT $ do
                   v <- evr
                   j <- spr
                   mrgReturn (v, j)
            case r of
              Left AssumptionViolation -> con False
              Left AssertionViolation -> con True
              Right (a, v) -> return $ nots $ v ==~ a
      -- print "CHECK"
      -- print evaluated
      -- print inputs
      -- print spr
      r <- solve config negphi
      -- print r
      -- case r of
      --   Right newm ->
      --     print $ evaluateSym True newm inputs
      --   _ -> return ()
      return $ do
        m <- r
        let newm = exact forallSymbols m
        let spre = evaluateSym True newm spr
        case spre of
          ExceptT (SingleU (Right v)) -> do
            return (evaluateSym True newm inputs, v, newm)
          _ -> error "Bad"
    guess :: Model -> a -> SymBiMap -> SBVC.Query (SymBiMap, Either SolvingFailure Model)
    guess candidate candidater origm = do
      -- liftIO $ print "GUESS"
      -- liftIO $ print candidater
      let SymBool evaluated = rm candidate candidater -- evaluateSym False candidate phi
      let (lowered, newm) = lowerSinglePrim' config evaluated origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          -- liftIO $ print $ evaluateSym True model $ fst i1
          -- liftIO $ print $ evaluateSym True model $ inputs
          return (newm, Right $ exceptFor exceptSymbols model)
        _ -> return (newm, Left $ sbvCheckSatResult r)
    loop ::
      Either SolvingFailure Model ->
      [[[a]]] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([[[a]]], Model))
    loop (Right mo) cexs origm = do
      r <- liftIO $ check mo
      case r of
        Left Unsat -> return (origm, Right (cexs, mo))
        Left v -> return (origm, Left v)
        Right (cex, cexr, cexm) -> do
          (newm, res) <- guess cexm cexr origm
          loop res (cex : cexs) newm
    loop (Left v) _ origm = return (origm, Left v)

cegisCustomized ::
  forall n a.
  (ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a) =>
  GrisetteSMTConfig n ->
  (a -> SymBool) ->
  [a] ->
  MiniProg ->
  FuncMap a ->
  M a ->
  IO (Either SolvingFailure ([[a]], Model))
cegisCustomized config spec inputs prog funcMap gen = SBV.runSMTWith (sbvConfig config) $ do
  let SymBool t = phi
  (newm, a) <- lowerSinglePrim config t
  SBVC.query $
    snd <$> do
      SBV.constrain a
      r <- SBVC.checkSat
      mr <- case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          return $ Right $ parseModel config md newm
        _ -> return $ Left $ sbvCheckSatResult r
      loop (exceptFor exceptSymbols <$> mr) [] newm
  where
    forallSymbols :: SymbolSet
    forallSymbols = extractSymbolics inputs
    i :: M a
    i = interpretMiniProg inputs prog funcMap gen
    i1 :: (UnionM (Either VerificationConditions a), IntermediateVarSet)
    i1 = simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT i "ep"
    i1r1 :: ExceptT VerificationConditions UnionM ()
    i1r1 = do
      x <- ExceptT $ fst i1
      symAssert $ spec x
    i1i :: IntermediateVarSet
    i1i = snd i1

    exceptSymbols :: SymbolSet
    exceptSymbols = extractSymbolics inputs <> case i1i of IntermediateVarSet v -> v

    phi = simpleMerge $ do
      v <- runExceptT i1r1
      con $ isRight v

    check :: Model -> IO (Either SolvingFailure ([a], Model))
    check candidate = do
      let evaluated :: CMiniProg = evaluateSymToCon candidate prog
      let evr :: ExceptT VerificationConditions UnionM a = interpretCMiniProg inputs evaluated funcMap

      let negphi = simpleMerge $ do
            v <- runExceptT evr
            case v of
              Left AssumptionViolation -> con False
              Left AssertionViolation -> con True
              Right a -> return $ nots $ spec a
      r <- solve config negphi
      print r
      return $ do
        m <- r
        let newm = exact forallSymbols m
        return (evaluateSym False newm inputs, newm)
    guess :: Model -> SymBiMap -> SBVC.Query (SymBiMap, Either SolvingFailure Model)
    guess candidate origm = do
      let SymBool evaluated = evaluateSym False candidate phi
      let (lowered, newm) = lowerSinglePrim' config evaluated origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          return (newm, Right $ exceptFor exceptSymbols model)
        _ -> return (newm, Left $ sbvCheckSatResult r)
    loop ::
      Either SolvingFailure Model ->
      [[a]] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([[a]], Model))
    loop (Right mo) cexs origm = do
      r <- liftIO $ check mo
      case r of
        Left Unsat -> return (origm, Right (cexs, mo))
        Left v -> return (origm, Left v)
        Right (cex, cexm) -> do
          (newm, res) <- guess cexm origm
          loop res (cex : cexs) newm
    loop (Left v) _ origm = return (origm, Left v)