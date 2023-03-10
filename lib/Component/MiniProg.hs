module Component.MiniProg where

import Component.IntermediateVarSet
import Control.Monad.Except
import Control.Monad.Writer
import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as M
import GHC.Generics
import Grisette
import Common.Val

data Node
  = Node B.ByteString (UnionM Val) [UnionM Val]
  deriving (Generic, Show)
  deriving (Mergeable, SEq, EvaluateSym) via (Default Node)

nodeOutputIdx :: Node -> UnionM Val
nodeOutputIdx (Node _ o _) = o

data MiniProg = MiniProg {nodes :: [Node], output :: UnionM Val}
  deriving (Generic, Show)
  deriving (EvaluateSym, SEq) via (Default MiniProg)

data ComponentSpec = ComponentSpec {componentOp :: B.ByteString, componentInput :: Int}
  | RestrictedSpec {rcomponentOp :: B.ByteString, rcomponentInput :: Int, routputs :: Maybe [Int], rinputs :: Maybe [Val]}

data NodeSpec = NodeSpec {componentInfo :: ComponentSpec, globalInputNum :: Int, globalSlotNum :: Int}

data MiniProgSpec = MiniProgSpec {componentSpec :: [ComponentSpec], inputNum :: Int}

instance GenSymSimple NodeSpec Node where
  simpleFresh (NodeSpec (ComponentSpec op ii) gi si) = do
    o <- chooseFresh [0 .. si - 1]
    i <- simpleFresh (SimpleListSpec ii (ValSpec gi si))
    return $ Node op (mrgReturn $ Internal o) i
  simpleFresh (NodeSpec (RestrictedSpec op ii ro ri) gi si) = do
    o <- case ro of Nothing -> chooseFresh [0..si-1]; Just r -> chooseFresh r
    i <- case ri of Nothing -> simpleFresh (SimpleListSpec ii (ValSpec gi si)); Just r -> simpleFresh (SimpleListSpec ii (ChooseSpec r))
    return $ Node op (mrgReturn $ Internal o) i

instance GenSymSimple MiniProgSpec MiniProg where
  simpleFresh (MiniProgSpec c i) = do
    let specs = [NodeSpec c1 i (length c) | c1 <- c]
    o <- chooseFresh [0 .. length c - 1]
    flip MiniProg (mrgReturn $ Internal o) <$> traverse simpleFresh specs

{-
lessProg :: (MonadUnion m, MonadError VerificationConditions m) => MiniProg -> m ()
lessProg p = go (nodes p)
  where
    go [] = return ()
    go (Node _ _ [l,r]:vs) = do
      symAssert $ l <=~ r
      go vs
    go (Node _ _ _:vs) = go vs
    -}

acyclicProg :: (MonadUnion m, MonadError VerificationConditions m) => MiniProg -> m ()
acyclicProg p = go (nodes p)
  where
    go [] = mrgReturn ()
    go (Node _ vo vis : vs) = do
      go1 vo vis
      go vs
    go1 _ [] = mrgReturn ()
    go1 vo (vi : vis) = do
      symAssert (vi <~ vo)
      {-
        ( simpleMerge $ do
            vi' <- vi
            case vi' of
              Internal i -> return $ i <~ vo
              _ -> return (con True)
        )-}
      go1 vo vis

noDuplicateOutputProg :: (MonadUnion m, MonadError VerificationConditions m) => MiniProg -> m ()
noDuplicateOutputProg p = go (nodes p)
  where
    go [] = mrgReturn ()
    go (n : vs) = do
      go1 (nodeOutputIdx n) vs
      go vs
    go1 _ [] = mrgReturn ()
    go1 vo (n : vs) = do
      symAssert (vo /=~ nodeOutputIdx n)
      go1 vo vs

type EnhancedOutput a = (a, UnionM Val)

type EnhancedInput a = (a, UnionM Val)

data EnhancedNode a
  = EnhancedNode B.ByteString (EnhancedOutput a) [EnhancedInput a]
  | InputNode a Int
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (EnhancedNode a))

data EnhancedMiniProg a = EnhancedMiniProg {enhancedNodes :: [EnhancedNode a], enhancedOutput :: UnionM Val}
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (EnhancedMiniProg a))

genEnhancedMiniProg :: (MonadFresh m, MonadUnion m, MonadWriter IntermediateVarSet m, ExtractSymbolics a) => [a] -> MiniProg -> m a -> m (EnhancedMiniProg a)
genEnhancedMiniProg inputs (MiniProg prog outputIdx) intermediateGen = flip EnhancedMiniProg outputIdx <$> ((++) <$> goInputs 0 inputs <*> go prog)
  where
    goInputs _ [] = return []
    goInputs pos (x : xs) = do
      r <- goInputs (pos + 1) xs
      return (InputNode x pos : r)
    go [] = return []
    go (Node op pos nodeInputs : xs) = do
      r <- go xs
      g <- traverse (const intermediateGen) [0 .. length nodeInputs]
      let (ret : input1) = g
      tell $ IntermediateVarSet $ extractSymbolics (ret, input1)
      return (EnhancedNode op (ret, pos) (zip input1 nodeInputs) : r)

-- result_*, input_* are indices /
-- result_i = someOp ...
-- result_j = someOp input_j_1 input_j_2

-- enhanced:
-- value_i = someOp
-- value_j = someOp input_value_j_1 input_value_j_2

-- connected condition
-- result_i == input_j_1 `implies` value_i ==~ input_value_j_1

-- value_j = someOp (ite (= result_1 input_j_1) value_1 (ite (= result_2 input_j_1)) value_2 ...) (...)

connected ::
  forall m a.
  (MonadUnion m, MonadError VerificationConditions m, SEq a) =>
  EnhancedMiniProg a ->
  m ()
connected (EnhancedMiniProg enodes _) =
  mrgTraverse_
    ( \((ov, oi), (iv, ii)) ->
        symAssert ((oi ==~ ii) `implies` (ov ==~ iv))
    )
    $ [(o, i) | o <- outputs, i <- inputs]
  where
    outputs :: [(a, UnionM Val)]
    outputs =
      ( \case
          EnhancedNode _ (vo, vov) _ -> (vo, vov)
          InputNode vo vov -> (vo, mrgSingle $ Input $ mrgSingle vov)
      )
        <$> enodes
    inputs :: [(a, UnionM Val)]
    inputs =
      ( \case
          EnhancedNode _ _ vis -> vis
          _ -> []
      )
        =<< enodes

data Func a where
  Func :: (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => [a] -> m a) -> Func a

type Op = B.ByteString

type FuncMap a = M.HashMap Op (Func a)

interpretOp :: (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => Op -> FuncMap a -> [a] -> m a
interpretOp op fm args = case M.lookup op fm of
  Nothing -> mrgThrowError AssertionViolation
  Just (Func func) -> func args

semanticsCorrect :: (MonadUnion m, MonadError VerificationConditions m, SEq a, Mergeable a) => FuncMap a -> EnhancedMiniProg a -> m ()
semanticsCorrect fm (EnhancedMiniProg enodes _) = go enodes
  where
    go [] = mrgReturn ()
    go (InputNode {} : xs) = go xs
    go (EnhancedNode op (o, _) is : xs) = do
      interpretRes <- interpretOp op fm (fst <$> is)
      symAssert (interpretRes ==~ o)
      go xs

miniProgWellFormedConstraints :: (UnionLike m, MonadError VerificationConditions m) => MiniProg -> m ()
miniProgWellFormedConstraints prog = do
--  lessProg prog
  acyclicProg prog
  noDuplicateOutputProg prog

interpretMiniProg ::
  ( UnionLike m,
    MonadError VerificationConditions m,
    MonadFresh m,
    MonadWriter IntermediateVarSet m,
    ExtractSymbolics a,
    SEq a,
    Mergeable a
  ) =>
  [a] ->
  MiniProg ->
  FuncMap a ->
  m a ->
  m a
interpretMiniProg inputs prog fm intermediateGen = do
  enhanced <- genEnhancedMiniProg inputs prog intermediateGen
  connected enhanced
  semanticsCorrect fm enhanced
  let outputs = getOutputs enhanced
  go outputs (enhancedOutput enhanced)
  where
    getOutputs (EnhancedMiniProg enodes _) =
      ( \case
          EnhancedNode _ (vo, vr) _ -> [(vo, vr)]
          _ -> []
      )
        =<< enodes
    go [] _ = throwError AssertionViolation
    go ((xo,xr):xs) v = mrgIf (xr ==~ v) (mrgReturn xo) (go xs v)
