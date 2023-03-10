module Query where

import Control.Monad.Except
import Core
import Data.Hashable
import Data.Maybe
import Grisette
import Interpreter

synthV ::
  (ExtractSymbolics val, SimpleMergeable val, SEq val, ToCon val cval, EvaluateSym val, Eq val, Hashable val) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  [([[val]], val)] ->
  [[val]] ->
  val ->
  ([[val]] -> SymBool) ->
  ([[val]] -> val -> ExceptT VerificationConditions UnionM SymBool) ->
  Program val ->
  IO ([([[val]], val)], Maybe (ConProgram cval))
synthV config u b cexs inputs output inputSpace spec sketch = do
  m <- cegisExceptStdVC config (inputs, output) $ runExceptT $ do
    symAssume $ inputSpace inputs
    corr <- spec inputs output
    symAssume corr
    -- symAssume $ wellFormedProgram sketch
    mrgTraverse_
      ( \(i, o) -> do
          res <- interpretSketch u b sketch i
          symAssert $ res ==~ o
      )
      ((inputs, output) : cexs)
  case m of
    (r, Left _) -> return (r, Nothing)
    (r, Right mo) -> return (r, Just (evaluateSymToCon mo sketch))

synth ::
  (ExtractSymbolics val, SimpleMergeable val, SEq val, ToCon val cval, EvaluateSym val, Eq val, Hashable val) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  [[[val]]] ->
  [[val]] ->
  ([[val]] -> SymBool) ->
  ([[val]] -> ExceptT VerificationConditions UnionM val) ->
  Program val ->
  IO ([[[val]]], Maybe (ConProgram cval))
synth config u b cexs inputs inputSpace spec sketch = do
  m <- cegisExceptStdVC config inputs $ runExceptT $ do
    symAssume $ inputSpace inputs
    -- symAssume $ wellFormedProgram sketch
    mrgTraverse_
      ( \x -> do
          corr <- spec x
          res <- interpretSketch u b sketch x
          symAssert $ corr ==~ res
      )
      (inputs : cexs)
  case m of
    (r, Left _) -> return (r, Nothing)
    (r, Right mo) -> return (r, Just (evaluateSymToCon mo sketch))

verifyV ::
  (ExtractSymbolics val, SimpleMergeable val, SEq val, ToCon val cval, EvaluateSym val, Eq val, Hashable val) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  [[val]] ->
  val ->
  ([[val]] -> SymBool) ->
  ([[val]] -> val -> ExceptT VerificationConditions UnionM SymBool) ->
  Program val ->
  IO (Maybe [[cval]])
verifyV config u b inputs output inputSpace spec sketch = do
  m <- solveExcept config (\case (Left AssertionViolation) -> con True; _ -> con False) $ runExceptT $ do
    symAssume $ inputSpace inputs
    -- symAssume $ wellFormedProgram sketch
    corr <- spec inputs output
    symAssume corr
    res <- interpretSketch u b sketch inputs
    symAssert $ output ==~ res
  case m of
    Left _ -> return Nothing
    Right mo -> return $ Just (fmap (fromJust . toCon) <$> evaluateSym True mo inputs)

verify ::
  (ExtractSymbolics val, SimpleMergeable val, SEq val, ToCon val cval, EvaluateSym val, Eq val, Hashable val) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  [[val]] ->
  ([[val]] -> SymBool) ->
  ([[val]] -> ExceptT VerificationConditions UnionM val) ->
  Program val ->
  IO (Maybe [[cval]])
verify config u b inputs inputSpace spec sketch = do
  m <- solveExcept config (\case (Left AssertionViolation) -> con True; _ -> con False) $ runExceptT $ do
    symAssume $ inputSpace inputs
    -- symAssume $ wellFormedProgram sketch
    corr <- spec inputs
    res <- interpretSketch u b sketch inputs
    symAssert $ corr ==~ res
  case m of
    Left _ -> return Nothing
    Right mo -> return $ Just (fmap (fromJust . toCon) <$> evaluateSym True mo inputs)

synth1 ::
  forall n inputSpec val cval.
  ( GenSymSimple inputSpec val,
    ExtractSymbolics val,
    SimpleMergeable val,
    SEq val,
    ToSym cval val,
    ToCon val cval,
    EvaluateSym val,
    Show val,
    Eq val,
    Hashable val
  ) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  inputSpec ->
  ([[val]] -> SymBool) ->
  ([[val]] -> ExceptT VerificationConditions UnionM val) ->
  Program val ->
  IO (Maybe (ConProgram cval))
synth1 config u b inputSpec inputSpace spec sketch = go [] 3
  where
    go origCexs n = do
      print n
      let inputs = genSymSimple (SimpleListSpec n (SimpleListSpec (fromIntegral $ inputNum sketch) inputSpec)) "a" :: [[val]]
      (cexs, synthed) <- synth config u b origCexs inputs inputSpace spec sketch
      case synthed of
        Nothing -> do
          print cexs
          return Nothing
        Just cp -> do
          print cexs
          let inputs1 = genSymSimple (SimpleListSpec (n + 1) (SimpleListSpec (fromIntegral $ inputNum sketch) inputSpec)) "a" :: [[val]]
          v :: Maybe [[cval]] <- verify config u b inputs1 inputSpace spec (toSym cp)
          case v of
            Just _ -> go (cexs ++ origCexs) (n + 1)
            Nothing -> return $ Just cp

synth1V ::
  forall n inputSpec val cval.
  ( GenSymSimple inputSpec val,
    ExtractSymbolics val,
    SimpleMergeable val,
    SEq val,
    ToSym cval val,
    ToCon val cval,
    EvaluateSym val,
    Show val,
    Eq val,
    Hashable val
  ) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  inputSpec ->
  ([[val]] -> SymBool) ->
  ([[val]] -> val -> ExceptT VerificationConditions UnionM SymBool) ->
  Program val ->
  IO (Maybe (ConProgram cval))
synth1V config u b inputSpec inputSpace spec sketch = go [] 3
  where
    go origCexs n = do
      print n
      let inputs = genSymSimple (SimpleListSpec n (SimpleListSpec (fromIntegral $ inputNum sketch) inputSpec)) "i" :: [[val]]
      let output = genSymSimple inputSpec "o" :: val
      (cexs, synthed) <- synthV config u b origCexs inputs output inputSpace spec sketch
      case synthed of
        Nothing -> do
          print cexs
          return Nothing
        Just cp -> do
          print cexs
          let inputs1 = genSymSimple (SimpleListSpec (n + 1) (SimpleListSpec (fromIntegral $ inputNum sketch) inputSpec)) "i" :: [[val]]
          let output1 = genSymSimple inputSpec "o" :: val
          v :: Maybe [[cval]] <- verifyV config u b inputs1 output1 inputSpace spec (toSym cp)
          case v of
            Just _ -> go (cexs ++ origCexs) (n + 1)
            Nothing -> return $ Just cp
