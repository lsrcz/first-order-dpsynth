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

data AuxProg val a = AuxProg [a] [MiniProg val]
  deriving (Show, Generic)
  deriving (EvaluateSym) via Default (AuxProg val a)

numAux :: AuxProg val a -> Int
numAux (AuxProg i _) = length i

data AuxSpecInit a = AuxSpecInit [a] [MiniProgSpec]

instance GenSymSimple (AuxSpecInit a) (AuxProg SymInteger a) where
  simpleFresh (AuxSpecInit i m) = do
    miniprogs :: [MiniProg SymInteger] <- traverse simpleFresh m
    return $ AuxProg i miniprogs

instance (KnownNat n, 1 <= n) => GenSymSimple (AuxSpecInit a) (AuxProg (SymIntN n) a) where
  simpleFresh (AuxSpecInit i m) = do
    miniprogs :: [MiniProg (SymIntN n)] <- traverse simpleFresh m
    return $ AuxProg i miniprogs

instance GenSymSimple (AuxSpecInit a) (AuxProg (UnionM Val) a) where
  simpleFresh (AuxSpecInit i m) = do
    miniprogs :: [MiniProg val] <- traverse simpleFresh m
    return $ AuxProg i miniprogs

auxProgWellFormedConstraints ::
  (ValLike val, UnionLike m, MonadError VerificationConditions m) =>
  Int ->
  FuncMap a ->
  AuxProg val a ->
  m ()
auxProgWellFormedConstraints numInputs fm (AuxProg internalInits miniprogs) = do
  mrgTraverse_ (miniProgWellFormedConstraints (numInputs + length internalInits) fm) miniprogs

genIntermediates :: (Monad m, UnionLike m, Mergeable a) => Int -> Int -> [a] -> m a -> m [[a]]
genIntermediates num len inits intermediateGen = do
  v <- (traverse . traverse) (const intermediateGen) [[1 .. len] | _ <- [1 .. num]]
  mrgReturn $ uncurry (:) <$> zip inits v

interpretAuxProg ::
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
  AuxProg val a ->
  FuncMap a ->
  m a ->
  m [a]
interpretAuxProg inputs (AuxProg inits miniprogs) fm intermediateGen = do
  -- Env intermediates :: Env a <- simpleFresh (GenEnvSpec inputs inits spec (length miniprogs))
  intermediates <- genIntermediates (length inits) (length (head inputs)) inits intermediateGen
  go inputs intermediates miniprogs
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
