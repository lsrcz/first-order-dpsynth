module Component.ListCombProg where

import Component.MiniProg
import Grisette
import Common.Val (ValLike, CValLike, Val)
import Control.Monad.Except
import Component.IntermediateVarSet (IntermediateVarSet)
import Control.Monad.Writer
import Component.ListOps
import Component.ConcreteMiniProg
import GHC.Generics
import GHC.TypeLits
import Common.T

newtype ListCombProg val a = ListCombProg (MiniProg (MLOpCode a) val)
  deriving (Generic, Show)
  deriving (EvaluateSym) via (Default (ListCombProg val a))

newtype ListCombProgSpec a = ListCombProgSpec (MiniProgSpec (MLOpCode a))

instance GenSymSimple (ListCombProgSpec a) (ListCombProg SymInteger a) where
  simpleFresh (ListCombProgSpec m) = do
    miniprog :: MiniProg (MLOpCode a) SymInteger <- simpleFresh m
    return $ ListCombProg miniprog

instance (KnownNat n, 1 <= n) => GenSymSimple (ListCombProgSpec a) (ListCombProg (SymIntN n) a) where
  simpleFresh (ListCombProgSpec m) = do
    miniprog :: MiniProg (MLOpCode a) (SymIntN n) <- simpleFresh m
    return $ ListCombProg miniprog

instance GenSymSimple (ListCombProgSpec a) (ListCombProg (UnionM Val) a) where
  simpleFresh (ListCombProgSpec m) = do
    miniprog :: MiniProg (MLOpCode a) (UnionM Val) <- simpleFresh m
    return $ ListCombProg miniprog

interpretListMiniProg :: forall a val m.
  (ValLike val, MonadUnion m, MonadError VerificationConditions m, MonadFresh m,
    MonadWriter IntermediateVarSet m, ExtractSymbolics a, SEq a, Mergeable a, Show a, Show val) =>
  [a] -> MiniProg (MLOpCode a) val -> MLCombFuncMap a -> m (MT a) -> m (MT a)
interpretListMiniProg l = interpretMiniProg (mrgReturn . TInt <$> l)

interpretListCombProg :: forall a val m.
  (ValLike val, MonadUnion m, MonadError VerificationConditions m, MonadFresh m,
    MonadWriter IntermediateVarSet m, ExtractSymbolics a, SEq a, Mergeable a, Show a, Show val) =>
  [a] -> ListCombProg val a -> MLCombFuncMap a -> m (MT a) -> m a
interpretListCombProg l (ListCombProg prog) fm gen = do
  r <- interpretMiniProg (mrgReturn . TInt <$> l) prog fm gen
  v <- liftToMonadUnion r
  case v of
    TInt a -> mrgReturn a
    _ -> mrgThrowError AssertionViolation

listCombProgWellFormedConstraints ::
  (ValLike val, UnionLike m, MonadError VerificationConditions m, Show a, EvaluateSym a, ToCon a a) =>
  Int ->
  MLCombFuncMap a -> 
  ListCombProg val a ->
  m ()
listCombProgWellFormedConstraints numInputs fm (ListCombProg miniprogs) = do
  miniProgWellFormedConstraints numInputs fm miniprogs

newtype CListCombProg val c = CListCombProg (CMiniProg (CMLOpCode c) val)
  deriving (Generic, Show)

deriving via (Default (CListCombProg cval c))
  instance (ToCon val cval, ToCon s c) => ToCon (ListCombProg val s) (CListCombProg cval c)

interpretCListCombMiniProgOnConInputs :: CValLike cval =>
  [c] -> CMiniProg (CMLOpCode c) cval -> MLCombCFuncMap c -> Either VerificationConditions (CT c)
interpretCListCombMiniProgOnConInputs inputs = interpretCMiniProgOnConInputs (CInt <$> inputs)

interpretCListCombProgOnConInputs :: forall c cval. CValLike cval =>
  [c] -> CListCombProg cval c -> MLCombCFuncMap c -> Either VerificationConditions c
interpretCListCombProgOnConInputs inputs (CListCombProg prog) fm = do
  t <- interpretCListCombMiniProgOnConInputs inputs prog fm 
  case t of
    CInt c -> return c
    _ -> throwError AssertionViolation
