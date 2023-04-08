module Component.ConcreteProg where

import Common.Val
import Component.ConcreteMiniProg
import Component.Prog
import Control.Monad.Except
import GHC.Generics
import Grisette
import Component.AuxProg
import Data.List
import Common.FuncMap

data CAuxProg op cval c = CAuxProg [c] [CMiniProg op cval]
  deriving (Generic, Show)

deriving via (Default (CAuxProg op cval c))
  instance (ToCon op op, ToCon val cval, ToCon a c) =>
    (ToCon (AuxProg op val a) (CAuxProg op cval c))
  
data CProg op cval c = CProg (CAuxProg op cval c) (CMiniProg op cval)
  deriving (Generic, Show)

deriving via (Default (CProg op cval c))
  instance (ToCon op op, ToCon val cval, ToCon a c) =>
    (ToCon (Prog op val a) (CProg op cval c))

interpretCAuxProg ::
  forall m cval c a op fm.
  (CValLike cval, ToSym c a, MonadUnion m, Mergeable a,
   MonadError VerificationConditions m, FuncMapLike op a fm) =>
  [[a]] ->
  CAuxProg op cval c ->
  fm ->
  m [a]
interpretCAuxProg inputs (CAuxProg auxInits progs) fm = do
  go inputs (toSym <$> auxInits) progs
  where
    go :: [[a]] -> [a] -> [CMiniProg op cval] -> m [a]
    go currInputs currIntermediates _ | null (head currInputs) = mrgReturn currIntermediates
    go currInputs currIntermediates miniprogs = do
      r <- go1 ((head <$> currInputs) ++ currIntermediates) miniprogs
      go (tail <$> currInputs) r miniprogs
    go1 :: [a] -> [CMiniProg op cval] -> m [a]
    go1 i = mrgTraverse (\p -> interpretCMiniProg i p fm)

interpretCProg ::
  forall m cval c a op fm.
  (CValLike cval, ToSym c a, MonadUnion m, Mergeable a, MonadError VerificationConditions m,
  FuncMapLike op a fm) =>
  [[a]] ->
  CProg op cval c ->
    fm ->
  m a
interpretCProg inputs (CProg aux finalprog) fm = do
  r <- interpretCAuxProg inputs aux fm
  interpretCMiniProg r finalprog fm

interpretCProg' ::
  forall m cval c a op fm.
  (CValLike cval, ToSym c a, MonadUnion m, Mergeable a, MonadError VerificationConditions m,
  FuncMapLike op a fm) =>
  [[a]] ->
  CProg op cval c ->
  fm ->
  m [a]
interpretCProg' inputs (CProg (CAuxProg auxInits progs) finalprog) fm = do
  go inputs (toSym <$> auxInits) progs
  where
    go :: [[a]] -> [a] -> [CMiniProg op cval] -> m [a]
    go currInputs currIntermediates _ | null (head currInputs) =
      mrgFmap singleton $ interpretCMiniProg currIntermediates finalprog fm
    go currInputs currIntermediates miniprogs = do
      currResult <- interpretCMiniProg currIntermediates finalprog fm
      r <- go1 ((head <$> currInputs) ++ currIntermediates ++ [currResult]) miniprogs
      mrgFmap (currResult:) $ go (tail <$> currInputs) r miniprogs
    go1 :: [a] -> [CMiniProg op cval] -> m [a]
    go1 i = mrgTraverse (\p -> interpretCMiniProg i p fm)

