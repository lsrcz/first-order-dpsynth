module Component.AuxProg where

import Component.MiniProg
import Grisette
import GHC.Generics
import Common.Val
import GHC.TypeNats
import Control.Monad.Except
import GHC.Stack
import Control.Monad.Writer
import Component.IntermediateVarSet
import Common.FuncMap

data AuxProg op val a = AuxProg [a] [MiniProg op val]
  deriving (Show, Generic)
  deriving (EvaluateSym) via Default (AuxProg op val a)

numAux :: AuxProg op val a -> Int
numAux (AuxProg i _) = length i

data AuxSpecInit op a = AuxSpecInit [a] [MiniProgSpec op]

instance GenSymSimple (AuxSpecInit op a) (AuxProg op SymInteger a) where
  simpleFresh (AuxSpecInit i m) = do
    miniprogs :: [MiniProg op SymInteger] <- traverse simpleFresh m
    return $ AuxProg i miniprogs

instance (KnownNat n, 1 <= n) => GenSymSimple (AuxSpecInit op a) (AuxProg op (SymIntN n) a) where
  simpleFresh (AuxSpecInit i m) = do
    miniprogs :: [MiniProg op (SymIntN n)] <- traverse simpleFresh m
    return $ AuxProg i miniprogs

instance GenSymSimple (AuxSpecInit op a) (AuxProg op (UnionM Val) a) where
  simpleFresh (AuxSpecInit i m) = do
    miniprogs :: [MiniProg op (UnionM Val)] <- traverse simpleFresh m
    return $ AuxProg i miniprogs

auxProgWellFormedConstraints ::
  (ValLike val, UnionLike m, MonadError VerificationConditions m, FuncMapLike op a fm, OpCode op g) =>
  Int ->
  fm ->
  AuxProg op val a ->
  m ()
auxProgWellFormedConstraints numInputs fm (AuxProg internalInits miniprogs) = do
  mrgTraverse_ (miniProgWellFormedConstraints (numInputs + length internalInits) fm) miniprogs

genIntermediates :: (Monad m, UnionLike m, Mergeable a) => Int -> Int -> [a] -> m a -> m [[a]]
genIntermediates num len inits intermediateGen = do
  v <- (traverse . traverse) (const intermediateGen) [[1 .. len] | _ <- [1 .. num]]
  mrgReturn $ uncurry (:) <$> zip inits v

interpretAuxProg ::
  forall m val a op fm.
  ( HasCallStack,
    ValLike val,
    Show a,
    UnionLike m,
    MonadError VerificationConditions m,
    MonadWriter IntermediateVarSet m,
    MonadFresh m,
    ExtractSymbolics a,
    SEq a,
    Mergeable a,
    FuncMapLike op a fm, Show val, Show a, Show op
  ) =>
  [[a]] ->
  AuxProg op val a ->
  fm ->
  m a ->
  m [a]
interpretAuxProg inputs (AuxProg inits miniprogs) fm intermediateGen = do
  -- Env intermediates :: Env a <- simpleFresh (GenEnvSpec inputs inits spec (length miniprogs))
  intermediates <- genIntermediates (length inits) (length (head inputs)) inits intermediateGen
  go inputs intermediates miniprogs
  where
    go1 :: [a] -> [MiniProg op val] -> m [a]
    go1 l =
      mrgTraverse (\p -> interpretMiniProg l p fm intermediateGen)

    go :: [[a]] -> [[a]] -> [MiniProg op val] -> m [a]
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
