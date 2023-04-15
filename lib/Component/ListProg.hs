{-# LANGUAGE UndecidableInstances #-}

module Component.ListProg where

import Common.Val
import Component.ListAuxProg
import Component.ListOps
import Component.MiniProg
import Control.Monad.Except
import Grisette
import Control.Monad.Writer
import Component.IntermediateVarSet
import Common.ListProg
import Component.ConcreteMiniProg
import GHC.Generics

data ListProg val a = ListProg (ListAuxProg val a) (MiniProg (MLOpCode a) val)
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (ListProg val a))

data ListProgSpec a = ListProgSpec (ListAuxProgSpec a) (MiniProgSpec (MLOpCode a))

instance
  ( GenSymSimple (ListAuxProgSpec a) (ListAuxProg val a),
    GenSymSimple (MiniProgSpec (MLOpCode a)) (MiniProg (MLOpCode a) val)
  ) =>
  GenSymSimple (ListProgSpec a) (ListProg val a)
  where
  simpleFresh (ListProgSpec m p) = do
    auxprog :: ListAuxProg val a <- simpleFresh m
    finalprog <- simpleFresh p
    return $ ListProg auxprog finalprog

listProgWellFormedConstraints ::
  ( ValLike val,
    UnionLike m,
    MonadError VerificationConditions m,
    Show a,
    EvaluateSym a,
    ToCon a a
  ) =>
  Int ->
  MLFuncMap a ->
  ListProg val a ->
  m ()
listProgWellFormedConstraints numInputs fm (ListProg aux@(ListAuxProg l) finalprog) = do
  listAuxProgWellFormedConstraints numInputs fm aux
  miniProgWellFormedConstraints (length l) fm finalprog

interpretListProg :: forall a val m.
  (ValLike val, MonadUnion m, MonadError VerificationConditions m, MonadFresh m,
    MonadWriter IntermediateVarSet m, ExtractSymbolics a, SEq a, Mergeable a, Show a, Show val) =>
  [[a]] -> ListProg val a -> MLFuncMap a -> (Int -> m (MListProgVal a)) -> m a
interpretListProg l (ListProg aux finalprog) fm gen = do
  auxRes <- interpretListAuxProg l aux fm gen
  r <- interpretMiniProg (mrgReturn . LInt <$> auxRes) finalprog fm (gen 0)
  r1 <- liftToMonadUnion r
  case r1 of
    LInt a -> mrgReturn a
    _ -> mrgThrowError AssertionViolation

data CListProg val c = CListProg (CListAuxProg val c) (CMiniProg (CMLOpCode c) val)
  deriving (Generic, Show)

deriving via (Default (CListProg cval c))
  instance (ToCon val cval, ToCon s c) => ToCon (ListProg val s) (CListProg cval c)

interpretCListProgOnConInputs :: forall c cval. CValLike cval =>
  [[c]] -> CListProg cval c -> MLCFuncMap c -> Either VerificationConditions c
interpretCListProgOnConInputs inputs (CListProg aux finalprog) fm = do
  auxRes <- interpretCListAuxProgOnConInputs inputs aux fm
  r <- interpretCMiniProgOnConInputs (CLInt <$> auxRes) finalprog fm
  case r of
    CLInt c -> return c
    _ -> throwError AssertionViolation
