{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Component.ConcreteMiniProg where
import qualified Data.ByteString as B
import Component.MiniProg
import GHC.Generics
import Grisette
import Data.List (sortBy, partition)
import qualified Data.HashMap.Strict as M
import Control.Monad.Except
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Grisette.Backend.SBV.Data.SMT.Lowering
import Control.DeepSeq
import Data.Hashable
import Language.Haskell.TH.Syntax
import Control.Exception
import Control.Monad.Writer
import Component.IntermediateVarSet
import Data.Bifunctor

data CVal
  = CInternal Int
  | CInput Int
  deriving (Generic)
  deriving (ToCon Val) via (Default CVal)

data CNode = CNode B.ByteString Int [CVal]
  deriving (Generic)
  deriving (ToCon Node) via (Default CNode)

data CMiniProg = CMiniProg { cnodes :: [CNode], output :: Int }
  deriving (Generic)
  deriving (ToCon MiniProg) via (Default CMiniProg)

interpretCMiniProg :: (MonadUnion m, Mergeable a, MonadError VerificationConditions m) => [a] -> CMiniProg -> FuncMap a -> m a
interpretCMiniProg inputs (CMiniProg ns o) fm = go [] s
  where
    getOutputIdx (CNode _ r _) = r
    oidx = getOutputIdx (ns !! o)
    s = sortBy (\(CNode _ r1 _) (CNode _ r2 _) -> compare r1 r2) ns
    getNodeInputValue _ (CInput i) = inputs !! i
    getNodeInputValue reg (CInternal i) = reg !! i
    go reg [] = mrgReturn $ reg !! oidx
    go reg (CNode op _ nodeInputs:xs) = do
      r <- case fm M.! op of Func f -> f $ getNodeInputValue reg <$> nodeInputs
      go (reg ++ [r]) xs

sbvCheckSatResult :: SBVC.CheckSatResult -> SolvingFailure
sbvCheckSatResult SBVC.Sat = error "Should not happen"
sbvCheckSatResult (SBVC.DSat msg) = DSat msg
sbvCheckSatResult SBVC.Unsat = Unsat
sbvCheckSatResult SBVC.Unk = Unk

type M a = FreshT (ExceptT VerificationConditions (WriterT IntermediateVarSet UnionM)) a

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
      case v of
        Left vc -> con False
        Right x0 -> con True
    
    -- phi = nots assertion &&~ nots assumption
    -- negphi = assertion &&~ nots assumption
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