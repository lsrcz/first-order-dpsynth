module Component.ConcreteProg where

import Component.ConcreteMiniProg
import Component.MiniProg
import Component.Prog
import Control.Monad.Except
import GHC.Generics
import Grisette
import Common.Val

data CProg cval c = CProg [c] [CMiniProg cval] (CMiniProg cval)
  deriving (Generic, Show)
  deriving (ToCon (Prog val a)) via (Default (CProg cval c))

interpretCProg ::
  forall m cval c a.
  (CValLike cval, ToSym c a, MonadUnion m, Mergeable a, MonadError VerificationConditions m) =>
  [[a]] ->
  CProg cval c ->
  FuncMap a ->
  m a
interpretCProg inputs (CProg inits progs finalprog) fm = do
  r <- go inputs (toSym <$> inits) progs
  interpretCMiniProg r finalprog fm
  where
    go :: [[a]] -> [a] -> [CMiniProg cval] -> m [a]
    go currInputs currIntermediates _ | null (head currInputs) = mrgReturn currIntermediates
    go currInputs currIntermediates miniprogs = do
      r <- go1 ((head <$> currInputs) ++ currIntermediates) miniprogs
      go (tail <$> currInputs) r miniprogs
    go1 :: [a] -> [CMiniProg cval] -> m [a]
    go1 i = mrgTraverse (\p -> interpretCMiniProg i p fm)
