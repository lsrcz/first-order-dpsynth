module Component.ConcreteProg where

import Common.FuncMap
import Common.Val
import Component.AuxProg
import Component.ConcreteMiniProg
import Component.Prog
import Control.Monad.Except
import GHC.Generics
import Grisette

data CAuxProg op cval c = CAuxProg [c] [CMiniProg op cval]
  deriving (Generic, Show)

deriving via
  (Default (CAuxProg cop cval c))
  instance
    (ToCon op cop, ToCon val cval, ToCon a c) =>
    (ToCon (AuxProg op val a) (CAuxProg cop cval c))

data CProg op cval c = CProg (CAuxProg op cval c) (CMiniProg op cval)
  deriving (Generic, Show)

deriving via
  (Default (CProg cop cval c))
  instance
    (ToCon op cop, ToCon val cval, ToCon a c) =>
    (ToCon (Prog op val a) (CProg cop cval c))

interpretCAuxProgOnSymInputs ::
  forall m cval c a op fm.
  ( CValLike cval,
    ToSym c a,
    MonadUnion m,
    MonadFresh m,
    Mergeable a,
    MonadError VerificationConditions m,
    FuncMapLike op a fm
  ) =>
  [[a]] ->
  CAuxProg op cval c ->
  fm ->
  m [a]
interpretCAuxProgOnSymInputs inputs (CAuxProg auxInits progs) fm = do
  go inputs (toSym <$> auxInits) progs
  where
    go :: [[a]] -> [a] -> [CMiniProg op cval] -> m [a]
    go currInputs currIntermediates _ | null (head currInputs) = mrgReturn currIntermediates
    go currInputs currIntermediates miniprogs = do
      r <- go1 ((head <$> currInputs) ++ currIntermediates) miniprogs
      go (tail <$> currInputs) r miniprogs
    go1 :: [a] -> [CMiniProg op cval] -> m [a]
    go1 i = mrgTraverse (\p -> interpretCMiniProgOnSymInputs i p fm)

interpretCAuxProgOnConInputs ::
  forall cval c op fm.
  (CValLike cval, CFuncMapLike op c fm) =>
  [[c]] ->
  CAuxProg op cval c ->
  fm ->
  Either VerificationConditions [c]
interpretCAuxProgOnConInputs inputs (CAuxProg auxInits progs) fm = do
  go inputs auxInits progs
  where
    go :: [[c]] -> [c] -> [CMiniProg op cval] -> Either VerificationConditions [c]
    go currInputs currIntermediates _ | null (head currInputs) = return currIntermediates
    go currInputs currIntermediates miniprogs = do
      r <- go1 ((head <$> currInputs) ++ currIntermediates) miniprogs
      go (tail <$> currInputs) r miniprogs
    go1 :: [c] -> [CMiniProg op cval] -> Either VerificationConditions [c]
    go1 i = traverse (\p -> interpretCMiniProgOnConInputs i p fm)

interpretCProgOnSymInputs ::
  forall m cval c a op fm.
  ( CValLike cval,
    ToSym c a,
    MonadUnion m,
    MonadFresh m,
    Mergeable a,
    MonadError VerificationConditions m,
    FuncMapLike op a fm
  ) =>
  [[a]] ->
  CProg op cval c ->
  fm ->
  m a
interpretCProgOnSymInputs inputs (CProg aux finalprog) fm = do
  r <- interpretCAuxProgOnSymInputs inputs aux fm
  interpretCMiniProgOnSymInputs r finalprog fm

interpretCProgOnConInputs ::
  forall c cval op fm.
  ( CValLike cval,
    CFuncMapLike op c fm
  ) =>
  [[c]] ->
  CProg op cval c ->
  fm ->
  Either VerificationConditions c
interpretCProgOnConInputs inputs (CProg aux finalprog) fm = do
  r <- interpretCAuxProgOnConInputs inputs aux fm
  interpretCMiniProgOnConInputs r finalprog fm

{-
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

-}