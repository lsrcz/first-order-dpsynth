module Component.CEGIS where

import Common.Timing
import Common.Val
import Component.ConcreteProg
import Component.IntermediateVarSet
import Component.Prog
import Control.Monad.Except
import Control.Monad.Writer
import Data.Bifunctor
import Data.Maybe
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Grisette
import Grisette.Backend.SBV.Data.SMT.Lowering
import Test.QuickCheck
import Data.Either
import Common.FuncMap

sbvCheckSatResult :: SBVC.CheckSatResult -> SolvingFailure
sbvCheckSatResult SBVC.Sat = error "Should not happen"
sbvCheckSatResult (SBVC.DSat msg) = DSat msg
sbvCheckSatResult SBVC.Unsat = Unsat
sbvCheckSatResult SBVC.Unk = Unk

type M a = FreshT (ExceptT VerificationConditions (WriterT IntermediateVarSet UnionM)) a

cegisCustomized' ::
  forall n cval val a c op fm g.
  (ValLike val, CValLike cval, ToCon a c,
  EvaluateSym val, ToCon val cval, ExtractSymbolics a, EvaluateSym a,
  Mergeable a, SEq a, Show a, ToSym a a, ToCon a a, FuncMapLike op a fm,
  EvaluateSym op, OpCode op g, ToCon op op) =>
  GrisetteSMTConfig n ->
  ([[a]] -> ExceptT VerificationConditions UnionM a) ->
  [[a]] ->
  Prog op val a ->
  fm ->
  M a ->
  IO (Either SolvingFailure ([[[a]]], CProg op cval c))
cegisCustomized' config spec inputs prog funcMap gen = SBV.runSMTWith ((sbvConfig config) {transcript = Just "guess.smt2"}) $ do
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
          (progWellFormedConstraints (length inputs) funcMap prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    f :: Int -> [[a]] -> (ExceptT VerificationConditions UnionM a, IntermediateVarSet)
    f idx input = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT (interpretProg input prog funcMap gen) (FreshIdentWithInfo "x" idx)

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
      let evaluated :: CProg op cval a = evaluateSymToCon candidate prog
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
      SBVC.Query (SymBiMap, Either SolvingFailure ([[[a]]], CProg op cval c))
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
  forall n cval val a c op fm g.
  (ValLike val, Show cval, CValLike cval, ToCon a c, EvaluateSym val,
   ToCon val cval, ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a,
   FuncMapLike op a fm,
  OpCode op g) =>
  GrisetteSMTConfig n ->
  ([[a]] -> ExceptT VerificationConditions UnionM a) ->
  [[[a]]] ->
  Prog op val a ->
  fm ->
  M a ->
  IO (Either SolvingFailure ([[[a]]], CProg op cval c))
cegisCustomized config spec inputs prog funcMap gen = SBV.runSMTWith (sbvConfig config) {transcript = Just "guess.smt2"} $ do
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
          (progWellFormedConstraints (length (head inputs)) funcMap prog :: ExceptT VerificationConditions UnionM ())
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
    check (nextInput : remainingInputs) candidate = do
      let evaluated :: CProg op cval a = evaluateSymToCon candidate prog
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
              return $ Right (evaluateSym True newm nextInput, nextInput : remainingInputs, v)
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
      SBVC.Query (SymBiMap, Either SolvingFailure ([[[a]]], CProg op cval c))
    loop idx (Right mo) remainingInputs cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check remainingInputs mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (cex, newRemainingInputs, cexr) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex cexr origm
          loop (idx + 1) res newRemainingInputs (cex : cexs) newm
    loop _ (Left v) _ _ origm = return (origm, Left v)

cegisQuickCheck ::
  forall n cval val a c op fm g.
  (ValLike val, Show cval, CValLike cval, ToCon a c, Show c, ToSym c a, Eq c, EvaluateSym val,
  ToCon val cval, ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a, Read c,
  FuncMapLike op a fm,
  OpCode op g) =>
  ([[a]] -> Prog op val a -> fm -> M a -> M a) ->
  GrisetteSMTConfig n ->
  ([[a]] -> ExceptT VerificationConditions UnionM a) ->
  Int ->
  Gen [[c]] ->
  Int ->
  Prog op val a ->
  fm ->
  M a ->
  IO (Either SolvingFailure ([[[a]]], CProg op cval c))
cegisQuickCheck interpreter config spec numInputs inputGen maxGenSize prog funcMap gen = SBV.runSMTWith (sbvConfig config) {transcript = Just "guess.smt2"} $ do
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
          (progWellFormedConstraints numInputs funcMap prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    f :: Int -> [[a]] -> (ExceptT VerificationConditions UnionM a, IntermediateVarSet)
    f idx input = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT (interpreter input prog funcMap gen) (FreshIdentWithInfo "x" idx)

    phiIO :: Int -> [[a]] -> a -> SymBool
    phiIO idx i o = simpleMerge $ do
      x <- runExceptT $ fst $ f idx i
      return $ x ==~ Right o

    check :: Int -> Model -> IO (Either SolvingFailure ([[a]], Int, a))
    check i _ | i > maxGenSize = return (Left Unsat)
    check i candidate = do
      let evaluated :: CProg op cval a = evaluateSymToCon candidate prog
      r <-
        quickCheckWithResult
          (stdArgs {maxSize = i, maxSuccess = 1000, chatty = False})
          ( forAll (resize i inputGen) $ \input ->
              let p = interpretCProg (toSym input) evaluated funcMap :: ExceptT VerificationConditions UnionM a
                  sp = spec (toSym input)
               in case (p, sp) of
                    (ExceptT (SingleU (Right v)), ExceptT (SingleU (Right sv))) -> (fromJust $ toCon v :: c) == fromJust (toCon sv)
                    _ -> error "Bad"
          )
      case r of
        Success {} -> check (i + 1) candidate
        Failure _ _ _ _ _ _ _ _ _ _ r _ _ -> do
          let input = toSym (read (head r) :: [[c]])
          -- let input = toSym $ unGen inputGen curSeed i
          case spec input of
            ExceptT (SingleU (Right v)) -> return $ Right (input, i, v)
            ExceptT (SingleU (Left AssumptionViolation)) -> check (i + 1) candidate

{-
          return $ Right (input, i, ; _ -> error "Bad")
          -}
        _ -> error "???"

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
          liftIO $ print (evaluateSymToCon model prog :: CProg op cval c)
          return (newm, Right model)
        _ -> return (newm, Left $ sbvCheckSatResult r)
    loop ::
      Int ->
      Either SolvingFailure Model ->
      Int ->
      -- [[[a]]] ->
      [[[a]]] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([[[a]]], CProg op cval c))
    loop idx (Right mo) curSize cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check curSize mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (cex, nextSize, cexr) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex cexr origm
          loop (idx + 1) res nextSize (cex : cexs) newm
    loop _ (Left v) _ _ origm = return (origm, Left v)

{-
cegisQuickCheckWithSpec ::
  forall n cval val a c.
  (ValLike val, Show cval, CValLike cval, ToCon a c, Show c, ToSym c a, Eq c, EvaluateSym val, ToCon val cval, ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a, Read c) =>
  ([[a]] -> Prog val a -> FuncMap a -> M a -> M a) ->
  GrisetteSMTConfig n ->
  ([[a]] -> ExceptT VerificationConditions UnionM a) ->
  Int ->
  Gen [[c]] ->
  Int ->
  Prog val a ->
  FuncMap a ->
  M a ->
  IO (Either SolvingFailure ([[[a]]], CProg cval c))
cegisQuickCheckWithSpec interpreter config spec numInputs inputGen maxGenSize prog funcMap gen = SBV.runSMTWith (sbvConfig config) {transcript = Just "guess.smt2"} $ do
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
          (progWellFormedConstraints numInputs funcMap prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    f :: Int -> [[a]] -> (ExceptT VerificationConditions UnionM a, IntermediateVarSet)
    f idx input = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT (interpreter input prog funcMap gen) (FreshIdentWithInfo "x" idx)

    phiIO :: Int -> [[a]] -> a -> SymBool
    phiIO idx i o = simpleMerge $ do
      x <- runExceptT $ fst $ f idx i
      return $ x ==~ Right o

    check :: Int -> Model -> IO (Either SolvingFailure ([[a]], Int, a))
    check i _ | i > maxGenSize = return (Left Unsat)
    check i candidate = do
      let evaluated :: CProg cval a = evaluateSymToCon candidate prog
      r <-
        quickCheckWithResult
          (stdArgs {maxSize = i, maxSuccess = 1000, chatty = False})
          ( forAll (resize i inputGen) $ \input ->
              let p = interpretCProg' (toSym input) evaluated funcMap :: ExceptT VerificationConditions UnionM [a]
                  sp = spec (toSym input)
               in case (p, sp) of
                    (ExceptT (SingleU (Right v)), ExceptT (SingleU (Right sv))) -> (fromJust $ toCon $ last v :: c) == fromJust (toCon sv)
                    _ -> error "Bad"
          )
      case r of
        Success {} -> check (i + 1) candidate
        Failure _ _ _ _ _ _ _ _ _ _ r _ _ -> do
          let input = toSym (read (head r) :: [[c]])
          -- let input = toSym $ unGen inputGen curSeed i
          case spec input of
            ExceptT (SingleU (Right v)) -> return $ Right (input, i, v)
            ExceptT (SingleU (Left AssumptionViolation)) -> check (i + 1) candidate


{-
          return $ Right (input, i, ; _ -> error "Bad")
          -}
        _ -> error "???"

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
          liftIO $ print (evaluateSymToCon model prog :: CProg cval c)
          return (newm, Right model)
        _ -> return (newm, Left $ sbvCheckSatResult r)
    loop ::
      Int ->
      Either SolvingFailure Model ->
      Int ->
      -- [[[a]]] ->
      [[[a]]] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([[[a]]], CProg cval c))
    loop idx (Right mo) curSize cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check curSize mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (cex, nextSize, cexr) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex cexr origm
          loop (idx + 1) res nextSize (cex : cexs) newm
    loop _ (Left v) _ _ origm = return (origm, Left v)
    -}

cegisQuickCheckAssert ::
  forall n cval val a c op fm g.
  (ValLike val, Show val, Show cval, CValLike cval, ToCon a c, Show c, ToSym c a, Eq c, EvaluateSym val, ToCon val cval,
   ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a, Read c,
  FuncMapLike op a fm,
  OpCode op g) =>

  GrisetteSMTConfig n ->
  ([[a]] -> ExceptT VerificationConditions UnionM a) ->
  Int ->
  Gen [[c]] ->
  Int ->
  Prog op val a ->
  fm ->
  M a ->
  IO (Either SolvingFailure ([[[a]]], CProg op cval c))
cegisQuickCheckAssert config spec numInputs inputGen maxGenSize prog funcMap gen = SBV.runSMTWith (sbvConfig config) {transcript = Just "guess.smt2"} $ do
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
          (progWellFormedConstraints numInputs funcMap prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    f :: Int -> [[a]] -> a -> (ExceptT VerificationConditions UnionM (), IntermediateVarSet)
    f idx input result = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT (assertProgResult input result prog funcMap gen) (FreshIdentWithInfo "x" idx)

    phiIO :: Int -> [[a]] -> a -> SymBool
    phiIO idx i o = simpleMerge $ do
      x <- runExceptT $ fst $ f idx i o
      mrgReturn $ con $ isRight x

    check :: Int -> Model -> IO (Either SolvingFailure ([[a]], Int, a))
    check i _ | i > maxGenSize = return (Left Unsat)
    check i candidate = do
      let evaluated :: CProg op cval a = evaluateSymToCon candidate prog
      r <-
        quickCheckWithResult
          (stdArgs {maxSize = i, maxSuccess = 1000, chatty = False})
          ( forAll (resize i inputGen) $ \input ->
              let p = interpretCProg (toSym input) evaluated funcMap :: ExceptT VerificationConditions UnionM a
                  sp = spec (toSym input)
               in case (p, sp) of
                    (ExceptT (SingleU (Right v)), ExceptT (SingleU (Right sv))) -> (fromJust $ toCon v :: c) == fromJust (toCon sv)
                    _ -> error "Bad"
          )
      case r of
        Success {} -> check (i + 1) candidate
        Failure _ _ _ _ _ _ _ _ _ _ r _ _ -> do
          let input = toSym (read (head r) :: [[c]])
          -- let input = toSym $ unGen inputGen curSeed i
          case spec input of
            ExceptT (SingleU (Right v)) -> return $ Right (input, i, v)
            ExceptT (SingleU (Left AssumptionViolation)) -> check (i + 1) candidate

{-
          return $ Right (input, i, ; _ -> error "Bad")
          -}
        _ -> error "???"

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
          liftIO $ print (evaluateSymToCon model prog :: CProg op cval c)
          return (newm, Right model)
        _ -> return (newm, Left $ sbvCheckSatResult r)
    loop ::
      Int ->
      Either SolvingFailure Model ->
      Int ->
      -- [[[a]]] ->
      [[[a]]] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([[[a]]], CProg op cval c))
    loop idx (Right mo) curSize cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check curSize mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (cex, nextSize, cexr) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex cexr origm
          loop (idx + 1) res nextSize (cex : cexs) newm
    loop _ (Left v) _ _ origm = return (origm, Left v)