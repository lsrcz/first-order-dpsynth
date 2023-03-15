module Component.MiniProg where

import Common.Val
import Component.IntermediateVarSet
import Control.Monad.Except
import Control.Monad.Writer
import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as M
import GHC.Generics
import GHC.TypeLits
import Grisette

data Node val
  = Node B.ByteString val [val]
  deriving (Generic, Show)
  deriving (Mergeable, SEq, EvaluateSym) via (Default (Node val))

nodeOutputIdx :: Node val -> val
nodeOutputIdx (Node _ o _) = o

data MiniProg val = MiniProg {nodes :: [Node val], output :: val}
  deriving (Generic, Show)
  deriving (EvaluateSym, SEq) via (Default (MiniProg val))

data ComponentSpec
  = ComponentSpec {componentOp :: B.ByteString, componentInput :: Int}
  | RestrictedSpec {rcomponentOp :: B.ByteString, rcomponentInput :: Int, routputs :: Maybe [Int], rinputs :: Maybe [Val]}

data NodeSpec = NodeSpec {componentInfo :: ComponentSpec, globalInputNum :: Int, globalSlotNum :: Int}

data MiniProgSpec = MiniProgSpec {componentSpec :: [ComponentSpec], inputNum :: Int}

instance GenSymSimple NodeSpec (Node SymInteger) where
  simpleFresh (NodeSpec (ComponentSpec op ii) _ _) = do
    o <- simpleFresh ()
    i <- simpleFresh (SimpleListSpec ii ())
    return $ Node op o i
  simpleFresh (NodeSpec (RestrictedSpec op ii _ _) gi si) = simpleFresh (NodeSpec (ComponentSpec op ii) gi si)

instance (KnownNat n, 1 <= n) => GenSymSimple NodeSpec (Node (SymIntN n)) where
  simpleFresh (NodeSpec (ComponentSpec op ii) _ _) = do
    o <- simpleFresh ()
    i <- simpleFresh (SimpleListSpec ii ())
    return $ Node op o i
  simpleFresh (NodeSpec (RestrictedSpec op ii _ _) gi si) = simpleFresh (NodeSpec (ComponentSpec op ii) gi si)

instance GenSymSimple NodeSpec (Node (UnionM Val)) where
  simpleFresh (NodeSpec (ComponentSpec op ii) gi si) = do
    o <- chooseFresh [0 .. si - 1]
    i <- simpleFresh (SimpleListSpec ii (ValSpec gi si))
    return $ Node op (mrgReturn $ Internal o) i
  simpleFresh (NodeSpec (RestrictedSpec op ii ro ri) gi si) = do
    o <- case ro of Nothing -> chooseFresh [0 .. si - 1]; Just r -> chooseFresh r
    i <- case ri of Nothing -> simpleFresh (SimpleListSpec ii (ValSpec gi si)); Just r -> simpleFresh (SimpleListSpec ii (ChooseSpec r))
    return $ Node op (mrgReturn $ Internal o) i

instance GenSymSimple MiniProgSpec (MiniProg SymInteger) where
  simpleFresh (MiniProgSpec c i) = do
    let specs = [NodeSpec c1 i (length c) | c1 <- c]
    o <- simpleFresh ()
    flip MiniProg o <$> traverse simpleFresh specs

instance (KnownNat n, 1 <= n) => GenSymSimple MiniProgSpec (MiniProg (SymIntN n)) where
  simpleFresh (MiniProgSpec c i) = do
    let specs = [NodeSpec c1 i (length c) | c1 <- c]
    o <- simpleFresh ()
    flip MiniProg o <$> traverse simpleFresh specs

instance GenSymSimple MiniProgSpec (MiniProg (UnionM Val)) where
  simpleFresh (MiniProgSpec c i) = do
    let specs = [NodeSpec c1 i (length c) | c1 <- c]
    o <- chooseFresh [0 .. length c - 1]
    flip MiniProg (mrgReturn $ Internal o) <$> traverse simpleFresh specs

boundProg :: (ValLike val, MonadUnion m, MonadError VerificationConditions m) => Int -> MiniProg val -> m ()
boundProg numInputs p = go (nodes p)
  where
    numSlots = length (nodes p)
    go [] = mrgReturn ()
    go (Node _ vo vis : vs) = do
      symAssert (boundVal (internalVal numInputs 0) (internalVal numInputs numSlots) vo)
      go1 vis
      go vs
    go1 [] = mrgReturn ()
    go1 (x : xs) = do
      symAssert (boundVal (inputVal 0) (internalVal numInputs numSlots) x)
      go1 xs

acyclicProg :: (ValLike val, MonadUnion m, MonadError VerificationConditions m) => MiniProg val -> m ()
acyclicProg p = go (nodes p)
  where
    go [] = mrgReturn ()
    go (Node _ vo vis : vs) = do
      go1 vo vis
      go vs
    go1 _ [] = mrgReturn ()
    go1 vo (vi : vis) = do
      symAssert (ltVal vi vo)
      go1 vo vis

binarySymmReduction :: (ValLike val, MonadUnion m, MonadError VerificationConditions m) => FuncMap a -> MiniProg val -> m ()
binarySymmReduction fm p = go (nodes p)
  where
    go [] = mrgReturn ()
    go (Node op _ vis : vs) = do
      let Func nop comm _ = fm M.! op
      when (nop == 2 && comm) $ symAssert (leVal (head vis) (vis !! 1))
      go vs

noDuplicateOutputProg :: (ValLike val, MonadUnion m, MonadError VerificationConditions m) => MiniProg val -> m ()
noDuplicateOutputProg p = go (nodes p)
  where
    go [] = mrgReturn ()
    go (n : vs) = do
      go1 (nodeOutputIdx n) vs
      go vs
    go1 _ [] = mrgReturn ()
    go1 vo (n : vs) = do
      symAssert (nots $ eqVal vo $ nodeOutputIdx n)
      go1 vo vs

type EnhancedOutput val a = (a, val)

type EnhancedInput val a = (a, val)

data EnhancedNode val a
  = EnhancedNode B.ByteString (EnhancedOutput val a) [EnhancedInput val a]
  | InputNode a Int
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (EnhancedNode val a))

data EnhancedMiniProg val a = EnhancedMiniProg {enhancedNodes :: [EnhancedNode val a], enhancedOutput :: val}
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (EnhancedMiniProg val a))

genEnhancedMiniProg :: forall val m a. (ValLike val, MonadFresh m, MonadUnion m, MonadWriter IntermediateVarSet m, ExtractSymbolics a) => [a] -> MiniProg val -> m a -> m (EnhancedMiniProg val a)
genEnhancedMiniProg inputs (MiniProg prog outputIdx) intermediateGen = flip EnhancedMiniProg outputIdx <$> ((++) <$> goInputs 0 inputs <*> go prog)
  where
    goInputs _ [] = return []
    goInputs pos (x : xs) = do
      r <- goInputs (pos + 1) xs
      return (InputNode x pos : r)
    go :: [Node val] -> m [EnhancedNode val a]
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
  forall m val a.
  (ValLike val, MonadUnion m, MonadError VerificationConditions m, SEq a) =>
  EnhancedMiniProg val a ->
  m ()
connected (EnhancedMiniProg enodes _) =
  mrgTraverse_
    ( \((ov, oi), (iv, ii)) ->
        symAssert (eqVal oi ii `implies` (ov ==~ iv))
    )
    $ [(o, i) | o <- outputs, i <- inputs]
  where
    outputs :: [(a, val)]
    outputs =
      ( \case
          EnhancedNode _ (vo, vov) _ -> (vo, vov)
          InputNode vo vov -> (vo, inputVal vov)
      )
        <$> enodes
    inputs :: [(a, val)]
    inputs =
      ( \case
          EnhancedNode _ _ vis -> vis
          _ -> []
      )
        =<< enodes

data Func a where
  Func :: Int -> Bool -> (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => [a] -> m a) -> Func a

type Op = B.ByteString

type FuncMap a = M.HashMap Op (Func a)

interpretOp :: (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => Op -> FuncMap a -> [a] -> m a
interpretOp op fm args = case M.lookup op fm of
  Nothing -> mrgThrowError AssertionViolation
  Just (Func _ _ func) -> func args

semanticsCorrect :: (MonadUnion m, MonadError VerificationConditions m, SEq a, Mergeable a) => FuncMap a -> EnhancedMiniProg val a -> m ()
semanticsCorrect fm (EnhancedMiniProg enodes _) = go enodes
  where
    go [] = mrgReturn ()
    go (InputNode {} : xs) = go xs
    go (EnhancedNode op (o, _) is : xs) = do
      interpretRes <- interpretOp op fm (fst <$> is)
      symAssert (interpretRes ==~ o)
      go xs

miniProgWellFormedConstraints :: (ValLike val, UnionLike m, MonadError VerificationConditions m) => Int -> FuncMap a -> MiniProg val -> m ()
miniProgWellFormedConstraints numInputs fm prog = do
  --  lessProg prog
  binarySymmReduction fm prog
  boundProg numInputs prog
  acyclicProg prog
  noDuplicateOutputProg prog

interpretMiniProg ::
  ( ValLike val,
    UnionLike m,
    MonadError VerificationConditions m,
    MonadFresh m,
    MonadWriter IntermediateVarSet m,
    ExtractSymbolics a,
    SEq a,
    Mergeable a
  ) =>
  [a] ->
  MiniProg val ->
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
    go ((xo, xr) : xs) v = mrgIf (eqVal xr v) (mrgReturn xo) (go xs v)
