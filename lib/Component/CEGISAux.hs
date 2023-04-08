module Component.CEGISAux where
import Common.Val
import Grisette
import Control.Monad.Except
import Test.QuickCheck
import Component.AuxProg
import Component.MiniProg
import Component.CEGIS (sbvCheckSatResult, M)
import Component.ConcreteProg
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Grisette.Backend.SBV.Data.SMT.Lowering
import Common.Timing
import Component.IntermediateVarSet
import Data.Bifunctor
import Control.Monad.Writer
import Data.Maybe
import GHC.Generics
import Debug.Trace

data DistinguishingInputs c =
  DistinguishingInputs [[c]] [[c]] [c]
  deriving (Generic, Show, Read)
  deriving (ToCon (DistinguishingInputs s)) via Default (DistinguishingInputs c)

deriving via Default (DistinguishingInputs s)
  instance ToSym c s => ToSym (DistinguishingInputs c) (DistinguishingInputs s)

cegisAuxQuickCheck ::
  forall n cval val a c.
  (ValLike val, Show cval, CValLike cval, ToCon a c, Show c, ToSym c a, Eq c, EvaluateSym val, ToCon val cval, ExtractSymbolics a, EvaluateSym a, Mergeable a, SEq a, Show a, ToSym a a, ToCon a a, Read c) =>
  GrisetteSMTConfig n ->
  ([[a]] -> ExceptT VerificationConditions UnionM a) ->
  Int ->
  Gen (DistinguishingInputs c) ->
  Int ->
  AuxProg val a ->
  FuncMap a ->
  M a ->
  IO (Either SolvingFailure ([DistinguishingInputs a], CAuxProg cval c))
cegisAuxQuickCheck config spec numInputs inputGen maxGenSize prog funcMap gen = SBV.runSMTWith (sbvConfig config) {transcript = Just "guess.smt2"} $ do
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
          (auxProgWellFormedConstraints numInputs funcMap prog :: ExceptT VerificationConditions UnionM ())
      return $ case v of
        Left _ -> con False
        Right _ -> con True

    f :: Int -> [[a]] -> (ExceptT VerificationConditions UnionM [a], IntermediateVarSet)
    f idx input = first ExceptT $ simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT (interpretAuxProg input prog funcMap gen) (FreshIdentWithInfo "x" idx)

    phiI :: Int -> [[a]] -> [[a]] -> SymBool
    phiI idx i1 i2 = simpleMerge $ do
      x1 <- runExceptT $ fst $ f (idx * 2) i1
      x2 <- runExceptT $ fst $ f (idx * 2 + 1) i2
      case (x1, x2) of
        (Right x1e, Right x2e) -> trace (show x1e) $ trace (show x2e) $ return $ x1e /=~ x2e
        _ -> con False

    check :: Int -> Model -> IO (Either SolvingFailure (DistinguishingInputs c, Int))
    check i _ | i > maxGenSize = return (Left Unsat)
    check i candidate = do
      let evaluated :: CAuxProg cval a = evaluateSymToCon candidate prog
      liftIO $ print evaluated
      r <-
        quickCheckWithResult
          (stdArgs {maxSize = i, maxSuccess = 1000, chatty = False})
          ( forAll (resize i inputGen) $ \(DistinguishingInputs i1 i2 v) ->
              let 
                i1v = zipWith (\l r -> l ++ [r]) i1 v
                i2v = zipWith (\l r -> l ++ [r]) i2 v
                p1 = interpretCAuxProg (toSym i1) evaluated funcMap :: ExceptT VerificationConditions UnionM [a]
                sp1 = spec (toSym i1v)
                p2 = interpretCAuxProg (toSym i2) evaluated funcMap :: ExceptT VerificationConditions UnionM [a]
                sp2 = spec (toSym i2v)
               in {-trace "-----" $ trace (show i1v) $ trace (show i2v) $
                 trace (show v) $ trace (show p1) $
                 trace (show sp1) $ trace (show p2) $
                 trace (show sp2) $-}
                 case (p1, sp1, p2, sp2) of
                    (ExceptT (SingleU (Right v1)), ExceptT (SingleU (Right sv1)),
                     ExceptT (SingleU (Right v2)), ExceptT (SingleU (Right sv2))) ->
                      let
                        cv1 = fromJust $ toCon v1 :: [c]
                        cv2 = fromJust $ toCon v2 :: [c]
                        csv1 = fromJust $ toCon sv1 :: c
                        csv2 = fromJust $ toCon sv2 :: c
                       in
                        csv1 == csv2 || cv1 /= cv2
                    _ -> error "Bad"
          )
      case r of
        Success {} -> check (i + 1) candidate
        Failure _ _ _ _ _ _ _ _ _ _ cex _ _ -> do
          let input :: DistinguishingInputs c = read (head cex) --unGen inputGen curSeed i
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
          let ep = evaluateSymToCon model prog :: CAuxProg cval c
          let r1 = interpretCAuxProg (toSym i1) ep funcMap :: ExceptT VerificationConditions UnionM [a]
          let r2 = interpretCAuxProg (toSym i2) ep funcMap :: ExceptT VerificationConditions UnionM [a]
          liftIO $ print ep
          liftIO $ print i1
          liftIO $ print i2
          liftIO $ print r1
          liftIO $ print r2
          return (newm, Right model)
        _ -> return (newm, Left $ sbvCheckSatResult r)
    
    loop ::
      Int ->
      Either SolvingFailure Model ->
      Int ->
      -- [[[a]]] ->
      [DistinguishingInputs a] ->
      SymBiMap ->
      SBVC.Query (SymBiMap, Either SolvingFailure ([DistinguishingInputs a], CAuxProg cval c))
    loop idx (Right mo) curSize cexs origm = do
      r <- liftIO $ timeItAll "CHECK" $ check curSize mo
      case r of
        Left Unsat -> return (origm, Right (cexs, evaluateSymToCon mo prog))
        Left v -> return (origm, Left v)
        Right (cex, nextSize) -> do
          (newm, res) <- timeItAll "GUESS" $ guess idx cex origm
          loop (idx + 1) res nextSize (toSym cex : cexs) newm
    loop _ (Left v) _ _ origm = return (origm, Left v)

