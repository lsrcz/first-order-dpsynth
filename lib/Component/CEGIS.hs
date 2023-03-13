module Component.CEGIS where

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
import Timing
import Common.Val
import Debug.Trace

sbvCheckSatResult :: SBVC.CheckSatResult -> SolvingFailure
sbvCheckSatResult SBVC.Sat = error "Should not happen"
sbvCheckSatResult (SBVC.DSat msg) = DSat msg
sbvCheckSatResult SBVC.Unsat = Unsat
sbvCheckSatResult SBVC.Unk = Unk

type M a = FreshT (ExceptT VerificationConditions (WriterT IntermediateVarSet UnionM)) a

cegisCustomized' ::
  forall n cval val a c.
  (ValLike val, CValLike cval, ToCon a c, EvaluateSym val, ToCon val cval, ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a) =>
  GrisetteSMTConfig n ->
  ([[a]] -> ExceptT VerificationConditions UnionM a) ->
  [[a]] ->
  Prog val a ->
  FuncMap a ->
  M a ->
  IO (Either SolvingFailure ([[[a]]], CProg cval c))
cegisCustomized' config spec inputs prog funcMap gen = SBV.runSMTWith (sbvConfig config) $ do
  let SymBool t = {-phiRight &&~-} wellFormed
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
      loop 1 mr [] newm
  where
    forallSymbols :: SymbolSet
    forallSymbols = extractSymbolics inputs

    wellFormed :: SymBool
    wellFormed = simpleMerge $ do
      v <-
        runExceptT
          (progWellFormedConstraints (length inputs) prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    f :: Int -> [[a]] -> (ExceptT VerificationConditions UnionM a, IntermediateVarSet)
    f idx input = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT (interpretProg input prog funcMap gen) (FreshIdentWithInfo "x" idx)
    (e0, _) = f 0 inputs

    phiIO :: Int -> [[a]] -> a -> SymBool
    phiIO idx i o = simpleMerge $ do
      x <- runExceptT $ fst $ f idx i
      return $ x ==~ Right o

{-
    phiRight = simpleMerge $ do
      v <- runExceptT e0
      con $ isRight v
      -}

    check :: Model -> IO (Either SolvingFailure ([[a]], a))
    check candidate = do
      let evaluated :: CProg cval a = evaluateSymToCon candidate prog
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
      r <- solve config negphi
      return $ do
        m <- r
        let newm = exact forallSymbols m
        let spre = evaluateSym True newm spr
        case spre of
          ExceptT (SingleU (Right v)) -> do
            return (evaluateSym True newm inputs, v)
          _ -> error "Bad"
    guess :: Int -> [[a]] -> a -> SymBiMap -> SBVC.Query (SymBiMap, Either SolvingFailure Model)
    guess idx candidatei candidateo origm = do
      liftIO $ print candidatei
      liftIO $ print candidateo
      let SymBool evaluated = phiIO idx candidatei candidateo
      (newm, lowered) <- lowerSinglePrimCached config evaluated origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          return (newm, Right model)
        _ -> return (newm, Left $ sbvCheckSatResult r)
    loop ::
      Int ->
      Either SolvingFailure Model ->
      [[[a]]] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([[[a]]], CProg cval c))
    loop idx (Right mo) cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (cex, cexr) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex cexr origm
          loop (idx + 1) res (cex : cexs) newm
    loop _ (Left v) _ origm = return (origm, Left v)

cegisCustomized ::
  forall n cval val a c.
  (ValLike val, CValLike cval, ToCon a c, EvaluateSym val, ToCon val cval, ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a) =>
  GrisetteSMTConfig n ->
  ([[a]] -> ExceptT VerificationConditions UnionM a) ->
  [[[a]]] ->
  Prog val a ->
  FuncMap a ->
  M a ->
  IO (Either SolvingFailure ([[[a]]], CProg cval c))
cegisCustomized config spec inputs prog funcMap gen = SBV.runSMTWith (sbvConfig config) $ do
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
      loop 1 mr inputs [] newm
  where
    forallSymbols :: SymbolSet
    forallSymbols = extractSymbolics inputs

    wellFormed :: SymBool
    wellFormed = simpleMerge $ do
      v <-
        runExceptT
          (progWellFormedConstraints (length (head inputs)) prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    f :: Int -> [[a]] -> (ExceptT VerificationConditions UnionM a, IntermediateVarSet)
    f idx input = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT (interpretProg input prog funcMap gen) (FreshIdentWithInfo "x" idx)

    phiIO :: Int -> [[a]] -> a -> SymBool
    phiIO idx i o = simpleMerge $ do
      x <- runExceptT $ fst $ f idx i
      return $ x ==~ Right o

    check :: [[[a]]] -> Model -> IO (Either SolvingFailure ([[a]], [[[a]]], a))
    check [] _ = return (Left Unsat)
    check (nextInput:remainingInputs) candidate = do
      let evaluated :: CProg cval a = evaluateSymToCon candidate prog
      let evr :: ExceptT VerificationConditions UnionM a = interpretCProg nextInput evaluated funcMap
      let spr :: ExceptT VerificationConditions UnionM a = spec nextInput

      let negphi = simpleMerge $ do
            r <- runExceptT $ do
              v <- evr
              j <- spr
              mrgReturn (v, j)
            case r of
              Left AssumptionViolation -> con False
              Left AssertionViolation -> con True
              Right (a, v) -> return $ nots $ v ==~ a
      r <- solve config negphi
      case r of
        Left sf -> case sf of
          Unsat -> check remainingInputs candidate
          err -> return (Left err)
        Right mo -> do
          let newm = exact forallSymbols mo
          let spre = evaluateSym True newm spr
          case spre of
            ExceptT (SingleU (Right v)) -> do
              return $ Right (evaluateSym True newm nextInput, nextInput:remainingInputs, v)
            _ -> error "Bad"

    guess :: Int -> [[a]] -> a -> SymBiMap -> SBVC.Query (SymBiMap, Either SolvingFailure Model)
    guess idx candidatei candidateo origm = do
      liftIO $ print candidatei
      liftIO $ print candidateo
      let SymBool evaluated = phiIO idx candidatei candidateo
      (newm, lowered) <- lowerSinglePrimCached config evaluated origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          return (newm, Right model)
        _ -> return (newm, Left $ sbvCheckSatResult r)
    loop ::
      Int ->
      Either SolvingFailure Model ->
      [[[a]]] ->
      [[[a]]] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([[[a]]], CProg cval c))
    loop idx (Right mo) remainingInputs cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check remainingInputs mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (cex, newRemainingInputs, cexr) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex cexr origm
          loop (idx + 1) res newRemainingInputs (cex : cexs) newm
    loop _ (Left v) _ _ origm = return (origm, Left v)
