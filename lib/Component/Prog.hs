{-# LANGUAGE UndecidableInstances #-}

module Component.Prog where

import Common.Val
import Component.AuxProg
import Component.IntermediateVarSet
import Component.MiniProg
import Control.Monad.Except
import Control.Monad.Writer
import GHC.Generics
import GHC.Stack
import Grisette
import qualified Data.ByteString as B
import Debug.Trace
import Data.List

data Prog val a = Prog (AuxProg val a) (MiniProg val)
  deriving (Show, Generic)
  deriving (EvaluateSym) via Default (Prog val a)

data ProgSpecInit a = ProgSpecInit [a] [MiniProgSpec] MiniProgSpec

instance
  ( GenSymSimple (AuxSpecInit a) (AuxProg val a),
    GenSymSimple MiniProgSpec (MiniProg val)
  ) =>
  GenSymSimple (ProgSpecInit a) (Prog val a)
  where
  simpleFresh (ProgSpecInit i m p) = do
    auxprog :: AuxProg val a <- simpleFresh (AuxSpecInit i m)
    finalprog <- simpleFresh p
    return $ Prog auxprog finalprog

{-
instance (KnownNat n, 1 <= n) => GenSymSimple (ProgSpecInit a) (Prog (SymIntN n) a) where
  simpleFresh (ProgSpecInit i m p) = do
    miniprogs :: [MiniProg (SymIntN n)] <- traverse simpleFresh m
    finalprog <- simpleFresh p
    return $ Prog i miniprogs finalprog

instance GenSymSimple (ProgSpecInit a) (Prog (UnionM Val) a) where
  simpleFresh (ProgSpecInit i m p) = do
    miniprogs :: [MiniProg val] <- traverse simpleFresh m
    finalprog <- simpleFresh p
    return $ Prog i miniprogs finalprog
    -}

progWellFormedConstraints ::
  (ValLike val, UnionLike m, MonadError VerificationConditions m) =>
  Int ->
  FuncMap a ->
  Prog val a ->
  m ()
progWellFormedConstraints numInputs fm (Prog aux finalprog) = do
  auxProgWellFormedConstraints numInputs fm aux
  miniProgWellFormedConstraints (numAux aux) fm finalprog

interpretProg ::
  forall m val a.
  ( HasCallStack,
    ValLike val,
    Show a,
    UnionLike m,
    MonadError VerificationConditions m,
    MonadWriter IntermediateVarSet m,
    MonadFresh m,
    ExtractSymbolics a,
    SEq a,
    Mergeable a
  ) =>
  [[a]] ->
  Prog val a ->
  FuncMap a ->
  m a ->
  m a
interpretProg inputs (Prog aux finalprog) fm intermediateGen = do
  -- Env intermediates :: Env a <- simpleFresh (GenEnvSpec inputs inits spec (length miniprogs))
  final <- interpretAuxProg inputs aux fm intermediateGen
  r <- interpretMiniProg final finalprog fm intermediateGen
  mrgReturn r

type EnhancedOutputL val a = ([a], val)

type EnhancedInputL val a = ([a], val)


data EnhancedNodeL val a
  = EnhancedNodeL B.ByteString (EnhancedOutputL val a) [EnhancedInputL val a]
  | InputNodeL [a] Int
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (EnhancedNodeL val a))

newtype EnhancedMiniProgL val a = EnhancedMiniProgL {enhancedNodesL :: [EnhancedNodeL val a]}
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (EnhancedMiniProgL val a))

genEnhancedMiniProgL :: forall val m a. (ValLike val, MonadFresh m, MonadUnion m, MonadWriter IntermediateVarSet m, ExtractSymbolics a) => [[a]] -> MiniProg val -> m a -> m (EnhancedMiniProgL val a)
genEnhancedMiniProgL inputs (MiniProg prog _ _) intermediateGen = EnhancedMiniProgL <$> ((++) <$> goInputs 0 inputs <*> go prog)
  where
    goInputs _ [] = return []
    goInputs pos (x : xs) = do
      r <- goInputs (pos + 1) xs
      return (InputNodeL x pos : r)
    go :: [Node val] -> m [EnhancedNodeL val a]
    go [] = return []
    go (Node op pos nodeInputs : xs) = do
      r <- go xs
      g <- (traverse . traverse) (const intermediateGen) [[1..length (head inputs)] | _ <- [0 .. length nodeInputs]]
      let (ret : input1) = g
      tell $ IntermediateVarSet $ extractSymbolics (ret, input1)
      return (EnhancedNodeL op (ret, pos) (zip input1 nodeInputs) : r)

nodeValuesEnhancedMiniProgL :: ValLike val => EnhancedMiniProgL val a -> [([a], val)]
nodeValuesEnhancedMiniProgL (EnhancedMiniProgL enodes) =
  ( \case
      EnhancedNodeL _ (vo, vov) _ -> (vo, vov)
      InputNodeL vo vov -> (vo, inputVal vov)
  )
    <$> enodes

connectedL ::
  forall m val a.
  (ValLike val, Show val, Show a, MonadUnion m, MonadError VerificationConditions m, SEq a) =>
  EnhancedMiniProgL val a ->
  m ()
connectedL e@(EnhancedMiniProgL enodes) = trace (show enodes) $ trace (show outputs) $ trace (show inputs) $
  mrgTraverse_
    ( \((ov, oi), (iv, ii)) ->
        symAssert (eqVal oi ii `implies` (ov ==~ iv))
    )
    $ [(o, i) | o <- outputs, i <- inputs]
  where
    outputs :: [([a], val)]
    outputs = nodeValuesEnhancedMiniProgL e
    inputs :: [([a], val)]
    inputs =
      ( \case
          EnhancedNodeL _ _ vis -> vis
          _ -> []
      )
        =<< enodes

semanticsCorrectL :: (MonadUnion m, Show a, Show val, MonadError VerificationConditions m, SEq a, Mergeable a) => FuncMap a -> EnhancedMiniProgL val a -> m ()
semanticsCorrectL fm (EnhancedMiniProgL enodes) = go enodes
  where
    go [] = mrgReturn ()
    go (InputNodeL {} : xs) = go xs
    go (EnhancedNodeL op (o, _) is : xs) = do
      interpretRes <- trace (show $ fst <$> is) $ mrgTraverse (interpretOp op fm) (transpose $ fst <$> is)
      trace ("int: " ++ show is ++ show interpretRes) $ symAssert (interpretRes ==~ o)
      go xs

assertMiniProgResultL ::
  forall val a m.
  ( ValLike val,
    UnionLike m,
    MonadError VerificationConditions m,
    MonadFresh m,
    MonadWriter IntermediateVarSet m,
    ExtractSymbolics a,
    SEq a,
    Mergeable a,
    Show a,
    Show val
  ) =>
  [[a]] ->
  [a] ->
  MiniProg val ->
  FuncMap a ->
  m a ->
  m ()
assertMiniProgResultL inputs outputs prog@(MiniProg _ outputIdx _) fm intermediateGen = do
  enhanced <- genEnhancedMiniProgL inputs prog intermediateGen
  let xxx = nodeValuesEnhancedMiniProgL enhanced
  trace (show enhanced) $ trace (show outputs) $ connectedL enhanced
  trace "???" $ semanticsCorrectL fm enhanced
  go xxx
  where
    go :: [([a], val)] -> m ()
    go [] = throwError AssertionViolation
    go ((i,v):xs) = do
      mrgIf (eqVal outputIdx v) (symAssert (i ==~ outputs)) (go xs)

assertAuxProgResult :: (UnionLike m, ValLike val,
 MonadError VerificationConditions m, MonadFresh m,
 MonadWriter IntermediateVarSet m, ExtractSymbolics a, SEq a,
 Mergeable a, Show a, Show val) =>
  [[a]]
  -> [[a]]
  -> AuxProg val a
  -> FuncMap a
  -> m a
  -> m ()
assertAuxProgResult inputs intermediates (AuxProg _ progs) fm intermediateGen = do
  let op = zip progs (fmap tail intermediates)
  mrgTraverse_ (\(p, i) -> assertMiniProgResultL (inputs ++ fmap init intermediates) i p fm intermediateGen) op

assertProgResult ::
  forall m val a.
  ( HasCallStack,
    ValLike val,
    Show a,
    UnionLike m,
    MonadError VerificationConditions m,
    MonadWriter IntermediateVarSet m,
    MonadFresh m,
    ExtractSymbolics a,
    SEq a,
    Mergeable a, Show val
  ) =>
  [[a]] ->
  a ->
  Prog val a ->
  FuncMap a ->
  m a ->
  m ()
assertProgResult inputs result (Prog aux@(AuxProg auxInits _) finalprog) fm intermediateGen = do
  intermediates <- genIntermediates (length auxInits) (length (head inputs)) auxInits intermediateGen
  trace ("--intermediates--: \n" ++ show intermediates) $ assertAuxProgResult inputs intermediates aux fm intermediateGen
  assertMiniProgResult (last <$> intermediates) result finalprog fm intermediateGen
