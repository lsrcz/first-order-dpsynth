module Component.ConcreteProg where

import Common.Val
import Component.ConcreteMiniProg
import Component.MiniProg
import Component.Prog
import Control.Monad.Except
import GHC.Generics
import Grisette
import Component.AuxProg
import Data.List

data CAuxProg cval c = CAuxProg [c] [CMiniProg cval]
  deriving (Generic, Show)
  deriving (ToCon (AuxProg val a)) via (Default (CAuxProg cval c))

data CProg cval c = CProg (CAuxProg cval c) (CMiniProg cval)
  deriving (Generic, Show)
  deriving (ToCon (Prog val a)) via (Default (CProg cval c))

interpretCAuxProg ::
  forall m cval c a.
  (CValLike cval, ToSym c a, MonadUnion m, Mergeable a, MonadError VerificationConditions m) =>
  [[a]] ->
  CAuxProg cval c ->
  FuncMap a ->
  m [a]
interpretCAuxProg inputs (CAuxProg inits progs) fm = do
  go inputs (toSym <$> inits) progs
  where
    go :: [[a]] -> [a] -> [CMiniProg cval] -> m [a]
    go currInputs currIntermediates _ | null (head currInputs) = mrgReturn currIntermediates
    go currInputs currIntermediates miniprogs = do
      r <- go1 ((head <$> currInputs) ++ currIntermediates) miniprogs
      go (tail <$> currInputs) r miniprogs
    go1 :: [a] -> [CMiniProg cval] -> m [a]
    go1 i = mrgTraverse (\p -> interpretCMiniProg i p fm)

interpretCProg ::
  forall m cval c a.
  (CValLike cval, ToSym c a, MonadUnion m, Mergeable a, MonadError VerificationConditions m) =>
  [[a]] ->
  CProg cval c ->
  FuncMap a ->
  m a
interpretCProg inputs (CProg aux finalprog) fm = do
  r <- interpretCAuxProg inputs aux fm
  interpretCMiniProg r finalprog fm

interpretCProg' ::
  forall m cval c a.
  (CValLike cval, ToSym c a, MonadUnion m, Mergeable a, MonadError VerificationConditions m) =>
  [[a]] ->
  CProg cval c ->
  FuncMap a ->
  m [a]
interpretCProg' inputs (CProg (CAuxProg inits progs) finalprog) fm = do
  go inputs (toSym <$> inits) progs
  where
    go :: [[a]] -> [a] -> [CMiniProg cval] -> m [a]
    go currInputs currIntermediates _ | null (head currInputs) =
      mrgFmap singleton $ interpretCMiniProg currIntermediates finalprog fm
    go currInputs currIntermediates miniprogs = do
      currResult <- interpretCMiniProg currIntermediates finalprog fm
      r <- go1 ((head <$> currInputs) ++ currIntermediates ++ [currResult]) miniprogs
      mrgFmap (currResult:) $ go (tail <$> currInputs) r miniprogs
    go1 :: [a] -> [CMiniProg cval] -> m [a]
    go1 i = mrgTraverse (\p -> interpretCMiniProg i p fm)

