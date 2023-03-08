module Component.Prog where

import Component.IntermediateVarSet
import Component.MiniProg
import Control.Monad.Except
import Control.Monad.Writer
import GHC.Generics
import GHC.Stack
import Grisette

genIntermediates :: (Monad m, UnionLike m, Mergeable a) => Int -> Int -> [a] -> m a -> m [[a]]
genIntermediates num len inits intermediateGen = do
  v <- (traverse . traverse) (const intermediateGen) [[1 .. len] | _ <- [1 .. num]]
  mrgReturn $ uncurry (:) <$> zip inits v

data Prog a = Prog [a] [MiniProg] MiniProg
  deriving (Show, Generic)
  deriving (EvaluateSym) via Default (Prog a)

data ProgSpec = ProgSpec [MiniProgSpec] MiniProgSpec

instance GenSymSimple spec a => GenSymSimple (spec, ProgSpec) (Prog a) where
  simpleFresh (spec, ProgSpec m p) = do
    i :: [a] <- simpleFresh (SimpleListSpec (length m) spec)
    miniprogs :: [MiniProg] <- traverse simpleFresh m
    finalprog <- simpleFresh p
    return $ Prog i miniprogs finalprog

data ProgSpecInit a = ProgSpecInit [a] [MiniProgSpec] MiniProgSpec

instance GenSymSimple (ProgSpecInit a) (Prog a) where
  simpleFresh (ProgSpecInit i m p) = do
    miniprogs :: [MiniProg] <- traverse simpleFresh m
    finalprog <- simpleFresh p
    return $ Prog i miniprogs finalprog

progWellFormedConstraints ::
  (UnionLike m, MonadError VerificationConditions m) =>
  Prog a ->
  m ()
progWellFormedConstraints (Prog _ miniprogs finalprog) =
  mrgTraverse_ miniProgWellFormedConstraints (finalprog : miniprogs)

interpretProg ::
  forall m a.
  ( HasCallStack,
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
  Prog a ->
  FuncMap a ->
  m a ->
  m a
interpretProg inputs (Prog inits miniprogs finalprog) fm intermediateGen = do
  -- Env intermediates :: Env a <- simpleFresh (GenEnvSpec inputs inits spec (length miniprogs))
  intermediates <- genIntermediates (length inits) (length (head inputs)) inits intermediateGen
  final <- go inputs intermediates miniprogs
  interpretMiniProg final finalprog fm intermediateGen
  where
    go1 :: [a] -> [MiniProg] -> m [a]
    go1 l =
      mrgTraverse (\p -> interpretMiniProg l p fm intermediateGen)

    go :: [[a]] -> [[a]] -> [MiniProg] -> m [a]
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
