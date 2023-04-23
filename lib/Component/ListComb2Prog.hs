module Component.ListComb2Prog where

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
import Component.ListAuxProg
import Test.QuickCheck

newtype ListComb2Prog val a = ListComb2Prog [MiniProg (MLOpCode a) val]
  deriving (Generic, Show)
  deriving EvaluateSym via Default (ListComb2Prog val a)

newtype ListComb2ProgSpec a = ListComb2ProgSpec [MiniProgSpec (MLOpCode a)]

instance GenSymSimple (ListComb2ProgSpec a) (ListComb2Prog SymInteger a) where
  simpleFresh (ListComb2ProgSpec m) = do
    miniprogs :: [MiniProg (MLOpCode a) SymInteger] <- traverse simpleFresh m
    return $ ListComb2Prog miniprogs

instance (KnownNat n, 1 <= n) => GenSymSimple (ListComb2ProgSpec a) (ListComb2Prog (SymIntN n) a) where
  simpleFresh (ListComb2ProgSpec m) = do
    miniprogs :: [MiniProg (MLOpCode a) (SymIntN n)] <- traverse simpleFresh m
    return $ ListComb2Prog miniprogs

instance GenSymSimple (ListComb2ProgSpec a) (ListComb2Prog (UnionM Val) a) where
  simpleFresh (ListComb2ProgSpec m) = do
    miniprogs :: [MiniProg (MLOpCode a) (UnionM Val)] <- traverse simpleFresh m
    return $ ListComb2Prog miniprogs

interpretListComb2Prog :: forall a val m.
  (ValLike val, MonadUnion m, MonadError VerificationConditions m, MonadFresh m,
    MonadWriter IntermediateVarSet m, ExtractSymbolics a, SEq a, Mergeable a, Show a, Show val) =>
  [a] -> [a] -> ListComb2Prog val a -> MLCombFuncMap a -> m (MT a) -> m [a]
interpretListComb2Prog inputs intermediates (ListComb2Prog progs) fm gen =
  mrgTraverse (\p -> do
    r <- interpretMiniProg (mrgReturn . TInt <$> (inputs ++ intermediates)) p fm gen
    v <- liftToMonadUnion r
    case v of
      TInt a -> mrgReturn a
      _ -> mrgThrowError AssertionViolation) progs

listComb2ProgWellFormedConstraints ::
  (ValLike val, UnionLike m, MonadError VerificationConditions m, Show a, EvaluateSym a, ToCon a a) =>
  Int ->
  MLCombFuncMap a -> 
  ListComb2Prog val a ->
  m ()
listComb2ProgWellFormedConstraints numInputs fm (ListComb2Prog miniprogs) = do
  mrgTraverse_ (miniProgWellFormedConstraints numInputs fm) miniprogs

newtype CListComb2Prog val c = CListComb2Prog [CMiniProg (CMLOpCode c) val]
  deriving (Generic, Show)

deriving via (Default (CListComb2Prog cval c))
  instance (ToCon val cval, ToCon s c) => ToCon (ListComb2Prog val s) (CListComb2Prog cval c)

{-
interpretCListCombMiniProgOnConInputs :: CValLike cval =>
  [c] -> CMiniProg (CMLOpCode c) cval -> MLCombCFuncMap c -> Either VerificationConditions (CT c)
interpretCListCombMiniProgOnConInputs inputs = interpretCMiniProgOnConInputs (CInt <$> inputs)
-}

interpretCListComb2ProgOnConInputs :: forall c cval. CValLike cval =>
  [c] -> [c] -> CListComb2Prog cval c -> MLCombCFuncMap c -> Either VerificationConditions [c]
interpretCListComb2ProgOnConInputs inputs intermediates (CListComb2Prog progs) fm =
  traverse (\p -> do
       t <- interpretCMiniProgOnConInputs (CInt <$> inputs ++ intermediates) p fm 
       case t of
         CInt c -> return c
         _ -> throwError AssertionViolation) progs

qcListComb2AgainstListAux ::
  forall v c.
  ( CValLike v,
    Integral c,
    Num c,
    Ord c,
    Show c
  ) =>
  Integer -> 
  Integer -> 
  Integer -> 
  CListAuxProg v c -> 
  CListComb2Prog v c -> 
  IO ()
qcListComb2AgainstListAux m off n aux@(CListAuxProg progs) comb2 =
  quickCheckWith (stdArgs {maxSuccess=1000}) (\(l1 :: [Integer]) ->
    let
      l = fromInteger . (\x -> x `mod` m - off) <$> take (fromInteger n) l1
      Right intermediate = interpretCListAuxProgOnConInputs [(init l)] aux listAuxcfuncMap
      res = interpretCListAuxProgOnConInputs [l] aux listAuxcfuncMap
      combRes = interpretCListComb2ProgOnConInputs [last l] intermediate comb2 listCombcfuncMap
     in (length l <= 1 || combRes == res)
  )