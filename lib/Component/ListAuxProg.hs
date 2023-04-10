module Component.ListAuxProg where
import Component.MiniProg
import Common.ListProg
import Grisette
import Common.Val (ValLike, CValLike, Val)
import Control.Monad.Except
import Component.IntermediateVarSet (IntermediateVarSet)
import Control.Monad.Writer
import Component.ListOps
import Component.ConcreteMiniProg
import GHC.Generics
import GHC.TypeLits

newtype ListAuxProg val a = ListAuxProg [MiniProg (MLOpCode a) val]
  deriving (Generic, Show)
  deriving (EvaluateSym) via (Default (ListAuxProg val a))

newtype ListAuxProgSpec a = ListAuxProgSpec [MiniProgSpec (MLOpCode a)]

instance GenSymSimple (ListAuxProgSpec a) (ListAuxProg SymInteger a) where
  simpleFresh (ListAuxProgSpec m) = do
    miniprogs :: [MiniProg (MLOpCode a) SymInteger] <- traverse simpleFresh m
    return $ ListAuxProg miniprogs

instance (KnownNat n, 1 <= n) => GenSymSimple (ListAuxProgSpec a) (ListAuxProg (SymIntN n) a) where
  simpleFresh (ListAuxProgSpec m) = do
    miniprogs :: [MiniProg (MLOpCode a) (SymIntN n)] <- traverse simpleFresh m
    return $ ListAuxProg miniprogs

instance GenSymSimple (ListAuxProgSpec a) (ListAuxProg (UnionM Val) a) where
  simpleFresh (ListAuxProgSpec m) = do
    miniprogs :: [MiniProg (MLOpCode a) (UnionM Val)] <- traverse simpleFresh m
    return $ ListAuxProg miniprogs

interpretListMiniProg :: forall a val m.
  (ValLike val, MonadUnion m, MonadError VerificationConditions m, MonadFresh m,
    MonadWriter IntermediateVarSet m, ExtractSymbolics a, SEq a, Mergeable a, Show a, Show val) =>
  [[a]] -> MiniProg (MLOpCode a) val -> MLFuncMap a -> (Int -> m (MListProgVal a)) -> m (MListProgVal a)
interpretListMiniProg l p fm gen = interpretMiniProg (mrgReturn . LIntList <$> l) p fm (gen $ length $ head l)

interpretListAuxProg :: forall a val m.
  (ValLike val, MonadUnion m, MonadError VerificationConditions m, MonadFresh m,
    MonadWriter IntermediateVarSet m, ExtractSymbolics a, SEq a, Mergeable a, Show a, Show val) =>
  [[a]] -> ListAuxProg val a -> MLFuncMap a -> (Int -> m (MListProgVal a)) -> m [a]
interpretListAuxProg l (ListAuxProg progs) fm gen = do
  t <- mrgTraverse (\p -> interpretListMiniProg l p fm gen) progs
  go t
  where
    go :: [MListProgVal a] -> m [a]
    go [] = mrgReturn []
    go (x:xs) = do
      r <- liftToMonadUnion x
      rs <- go xs
      case r of
        LInt a -> mrgReturn $ a:rs
        _ -> mrgThrowError AssertionViolation

listAuxProgWellFormedConstraints ::
  (ValLike val, UnionLike m, MonadError VerificationConditions m, Show a, EvaluateSym a, ToCon a a) =>
  Int ->
  MLFuncMap a -> 
  ListAuxProg val a ->
  m ()
listAuxProgWellFormedConstraints numInputs fm (ListAuxProg miniprogs) = do
  mrgTraverse_ (miniProgWellFormedConstraints numInputs fm) miniprogs

newtype CListAuxProg val c = CListAuxProg [CMiniProg (CMLOpCode c) val]
  deriving (Generic, Show)

deriving via (Default (CListAuxProg cval c))
  instance (ToCon val cval, ToCon s c) => ToCon (ListAuxProg val s) (CListAuxProg cval c)

interpretCListMiniProgOnConInputs :: CValLike cval =>
  [[c]] -> CMiniProg (CMLOpCode c) cval -> MLCFuncMap c -> Either VerificationConditions (CListProgVal c)
interpretCListMiniProgOnConInputs inputs = interpretCMiniProgOnConInputs (CLIntList <$> inputs)

interpretCListAuxProgOnConInputs :: forall c cval. CValLike cval =>
  [[c]] -> CListAuxProg cval c -> MLCFuncMap c -> Either VerificationConditions [c]
interpretCListAuxProgOnConInputs inputs (CListAuxProg progs) fm = do
  t <- traverse (\p -> interpretCListMiniProgOnConInputs inputs p fm) progs
  go t
  where
    go :: [CListProgVal c] -> Either VerificationConditions [c]
    go [] = return []
    go (x:xs) = do
      rs <- go xs
      case x of
        CLInt a -> return $ a:rs
        _ -> throwError AssertionViolation

