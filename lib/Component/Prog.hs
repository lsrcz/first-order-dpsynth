module Component.Prog where

import Common.Val
import Component.IntermediateVarSet
import Component.MiniProg
import Control.Monad.Except
import Control.Monad.Writer
import GHC.Generics
import GHC.Stack
import GHC.TypeLits
import Grisette

genIntermediates :: (Monad m, UnionLike m, Mergeable a) => Int -> Int -> [a] -> m a -> m [[a]]
genIntermediates num len inits intermediateGen = do
  v <- (traverse . traverse) (const intermediateGen) [[1 .. len] | _ <- [1 .. num]]
  mrgReturn $ uncurry (:) <$> zip inits v

data Prog val a = Prog [a] [MiniProg val] (MiniProg val)
  deriving (Show, Generic)
  deriving (EvaluateSym) via Default (Prog val a)

data ProgSpec = ProgSpec [MiniProgSpec] MiniProgSpec

instance GenSymSimple spec a => GenSymSimple (spec, ProgSpec) (Prog SymInteger a) where
  simpleFresh (spec, ProgSpec m p) = do
    i :: [a] <- simpleFresh (SimpleListSpec (length m) spec)
    miniprogs :: [MiniProg SymInteger] <- traverse simpleFresh m
    finalprog <- simpleFresh p
    return $ Prog i miniprogs finalprog

instance (GenSymSimple spec a, KnownNat n, 1 <= n) => GenSymSimple (spec, ProgSpec) (Prog (SymIntN n) a) where
  simpleFresh (spec, ProgSpec m p) = do
    i :: [a] <- simpleFresh (SimpleListSpec (length m) spec)
    miniprogs :: [MiniProg (SymIntN n)] <- traverse simpleFresh m
    finalprog <- simpleFresh p
    return $ Prog i miniprogs finalprog

instance GenSymSimple spec a => GenSymSimple (spec, ProgSpec) (Prog (UnionM Val) a) where
  simpleFresh (spec, ProgSpec m p) = do
    i :: [a] <- simpleFresh (SimpleListSpec (length m) spec)
    miniprogs :: [MiniProg (UnionM Val)] <- traverse simpleFresh m
    finalprog <- simpleFresh p
    return $ Prog i miniprogs finalprog

data ProgSpecInit a = ProgSpecInit [a] [MiniProgSpec] MiniProgSpec

instance GenSymSimple (ProgSpecInit a) (Prog SymInteger a) where
  simpleFresh (ProgSpecInit i m p) = do
    miniprogs :: [MiniProg SymInteger] <- traverse simpleFresh m
    finalprog <- simpleFresh p
    return $ Prog i miniprogs finalprog

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

progWellFormedConstraints ::
  (ValLike val, UnionLike m, MonadError VerificationConditions m) =>
  Int ->
  FuncMap a ->
  Prog val a ->
  m ()
progWellFormedConstraints numInputs fm (Prog internalInits miniprogs finalprog) = do
  mrgTraverse_ (miniProgWellFormedConstraints (numInputs + length internalInits) fm) miniprogs
  miniProgWellFormedConstraints (length internalInits) fm finalprog

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
interpretProg inputs (Prog inits miniprogs finalprog) fm intermediateGen = do
  -- Env intermediates :: Env a <- simpleFresh (GenEnvSpec inputs inits spec (length miniprogs))
  intermediates <- genIntermediates (length inits) (length (head inputs)) inits intermediateGen
  final <- go inputs intermediates miniprogs
  r <- interpretMiniProg final finalprog fm intermediateGen
  mrgReturn r
  where
    go1 :: [a] -> [MiniProg val] -> m [a]
    go1 l =
      mrgTraverse (\p -> interpretMiniProg l p fm intermediateGen)

    go :: [[a]] -> [[a]] -> [MiniProg val] -> m [a]
    go inputs' intermediates' pg = do
      let progInputs = head <$> inputs'
      let progIntermediates = head <$> intermediates'
      let progNextIntermediates = head . tail <$> intermediates'
      r <- go1 (progInputs ++ progIntermediates) pg
      symAssert (progNextIntermediates ==~ r)
      if length (head inputs') == 1
        then mrgReturn progNextIntermediates
        else do
          go (tail <$> inputs') (tail <$> intermediates') pg
