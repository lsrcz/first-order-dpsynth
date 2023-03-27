module OOPSLA.Query where

import Control.Monad.Except
import Data.Hashable
import Data.Maybe
import Grisette
import OOPSLA.Core
import OOPSLA.Interpreter

synthV ::
  (Show val, ExtractSymbolics val, SimpleMergeable val, SEq val, ToCon val cval, EvaluateSym val, Eq val, Hashable val) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  TernaryFuncMap val ->
  [([[val]], val)] ->
  [[val]] ->
  val ->
  ([[val]] -> SymBool) ->
  ([[val]] -> val -> ExceptT VerificationConditions UnionM SymBool) ->
  Program val ->
  IO ([([[val]], val)], Maybe (ConProgram cval))
synthV config u b t cexs inputs output inputSpace spec sketch = do
  m <- cegisExceptStdVC config (inputs, output) $ runExceptT $ do
    symAssume $ inputSpace inputs
    corr <- spec inputs output
    symAssume corr
    -- symAssume $ wellFormedProgram sketch
    mrgTraverse_
      ( \(i, o) -> do
          res <- interpretSketch u b t sketch i
          symAssert $ res ==~ o
      )
      ((inputs, output) : cexs)
  case m of
    (r, Left _) -> return (r, Nothing)
    (r, Right mo) -> return (r, Just (evaluateSymToCon mo sketch))

synth ::
  (Show val, ExtractSymbolics val, SimpleMergeable val, SEq val, ToCon val cval, EvaluateSym val, Eq val, Hashable val) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  TernaryFuncMap val ->
  [[[val]]] ->
  [[val]] ->
  ([[val]] -> SymBool) ->
  ([[val]] -> ExceptT VerificationConditions UnionM val) ->
  Program val ->
  IO ([[[val]]], Maybe (ConProgram cval))
synth config u b t cexs inputs inputSpace spec sketch = do
  m <- cegisExceptStdVC config inputs $ runExceptT $ do
    symAssume $ inputSpace inputs
    -- symAssume $ wellFormedProgram sketch
    mrgTraverse_
      ( \x -> do
          corr <- spec x
          res <- interpretSketch u b t sketch x
          symAssert $ corr ==~ res
      )
      (inputs : cexs)
  case m of
    (r, Left _) -> return (r, Nothing)
    (r, Right mo) -> return (r, Just (evaluateSymToCon mo sketch))

verifyV ::
  (Show val, ExtractSymbolics val, SimpleMergeable val, SEq val, ToCon val cval, EvaluateSym val, Eq val, Hashable val) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  TernaryFuncMap val ->
  [[val]] ->
  val ->
  ([[val]] -> SymBool) ->
  ([[val]] -> val -> ExceptT VerificationConditions UnionM SymBool) ->
  Program val ->
  IO (Maybe [[cval]])
verifyV config u b t inputs output inputSpace spec sketch = do
  m <- solveExcept config (\case (Left AssertionViolation) -> con True; _ -> con False) $ runExceptT $ do
    symAssume $ inputSpace inputs
    -- symAssume $ wellFormedProgram sketch
    corr <- spec inputs output
    symAssume corr
    res <- interpretSketch u b t sketch inputs
    symAssert $ output ==~ res
  case m of
    Left _ -> return Nothing
    Right mo -> return $ Just (fmap (fromJust . toCon) <$> evaluateSym True mo inputs)

verify ::
  (Show val, ExtractSymbolics val, SimpleMergeable val, SEq val, ToCon val cval, EvaluateSym val, Eq val, Hashable val) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  TernaryFuncMap val ->
  [[val]] ->
  ([[val]] -> SymBool) ->
  ([[val]] -> ExceptT VerificationConditions UnionM val) ->
  Program val ->
  IO (Maybe [[cval]])
verify config u b t inputs inputSpace spec sketch = do
  m <- solveExcept config (\case (Left AssertionViolation) -> con True; _ -> con False) $ runExceptT $ do
    symAssume $ inputSpace inputs
    -- symAssume $ wellFormedProgram sketch
    corr <- spec inputs
    res <- interpretSketch u b t sketch inputs
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
  TernaryFuncMap val ->
  inputSpec ->
  ([[val]] -> SymBool) ->
  ([[val]] -> ExceptT VerificationConditions UnionM val) ->
  Program val ->
  IO (Maybe (ConProgram cval))
synth1 config u b t inputSpec inputSpace spec sketch = go [] 3
  where
    go origCexs n = do
      print n
      let inputs = genSymSimple (SimpleListSpec (fromIntegral $ inputNum sketch) (SimpleListSpec n inputSpec)) "a" :: [[val]]
      (cexs, synthed) <- synth config u b t origCexs inputs inputSpace spec sketch
      case synthed of
        Nothing -> do
          print cexs
          return Nothing
        Just cp -> do
          print cexs
          let inputs1 = genSymSimple (SimpleListSpec (fromIntegral $ inputNum sketch) (SimpleListSpec (n + 1) inputSpec)) "a" :: [[val]]
          v :: Maybe [[cval]] <- verify config u b t inputs1 inputSpace spec (toSym cp)
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
  TernaryFuncMap val ->
  inputSpec ->
  ([[val]] -> SymBool) ->
  ([[val]] -> val -> ExceptT VerificationConditions UnionM SymBool) ->
  Program val ->
  IO (Maybe (ConProgram cval))
synth1V config u b t inputSpec inputSpace spec sketch = go [] 3
  where
    go origCexs n = do
      print n
      let inputs = genSymSimple (SimpleListSpec (fromIntegral $ inputNum sketch) (SimpleListSpec n inputSpec)) "i" :: [[val]]
      let output = genSymSimple inputSpec "o" :: val
      (cexs, synthed) <- synthV config u b t origCexs inputs output inputSpace spec sketch
      case synthed of
        Nothing -> do
          print cexs
          return Nothing
        Just cp -> do
          print cexs
          let inputs1 = genSymSimple (SimpleListSpec (fromIntegral $ inputNum sketch) (SimpleListSpec (n + 1) inputSpec)) "i" :: [[val]]
          let output1 = genSymSimple inputSpec "o" :: val
          v :: Maybe [[cval]] <- verifyV config u b t inputs1 output1 inputSpace spec (toSym cp)
          case v of
            Just _ -> go (cexs ++ origCexs) (n + 1)
            Nothing -> return $ Just cp
