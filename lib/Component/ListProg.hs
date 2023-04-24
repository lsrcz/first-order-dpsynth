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
import Component.ListCombProg
import Common.T
import Debug.Trace
import Test.QuickCheck

data ListProg val a = ListProg (ListAuxProg val a) (ListCombProg val a)
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (ListProg val a))

data ListProgSpec a = ListProgSpec (ListAuxProgSpec a) (ListCombProgSpec a)

instance
  ( GenSymSimple (ListAuxProgSpec a) (ListAuxProg val a),
    GenSymSimple (ListCombProgSpec a) (ListCombProg val a)
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
  MLCombFuncMap a ->
  ListProg val a ->
  m ()
listProgWellFormedConstraints numInputs fm combfm (ListProg aux@(ListAuxProg l) finalprog) = do
  listAuxProgWellFormedConstraints numInputs fm aux
  listCombProgWellFormedConstraints (length l + 1 + numInputs) combfm finalprog

interpretListProg :: forall a val m.
  (ValLike val, MonadUnion m, MonadError VerificationConditions m, MonadFresh m,
    MonadWriter IntermediateVarSet m, ExtractSymbolics a, SEq a, Mergeable a, Show a, Show val) =>
  [[a]] -> [a] -> ListProg val a -> MLFuncMap a -> MLCombFuncMap a -> (Int -> m (MListProgVal a)) -> m (MT a) -> m a
interpretListProg l prevRes (ListProg aux finalprog) fm combfm gen gent = do
  auxRes <- interpretListAuxProg (fmap init l) aux fm gen
  interpretListCombProg (prevRes++auxRes++fmap last l) finalprog combfm gent

data CListProg val c = CListProg (CListAuxProg val c) (CListCombProg val c)
  deriving (Generic, Show)

deriving via (Default (CListProg cval c))
  instance (ToCon val cval, ToCon s c) => ToCon (ListProg val s) (CListProg cval c)

interpretCListProgOnConInputs :: forall c cval. (Show c, CValLike cval) =>
  [[c]] -> [c] -> CListProg cval c -> MLCFuncMap c -> MLCombCFuncMap c -> Either VerificationConditions c
interpretCListProgOnConInputs inputs prevRes (CListProg aux finalprog) fm combfm = do
  auxRes <- interpretCListAuxProgOnConInputs (fmap init inputs) aux fm
  interpretCListCombProgOnConInputs (prevRes++auxRes++fmap last inputs) finalprog combfm

qcListProg1 ::
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
  Integer ->
  Integer ->
  ([Integer] -> Integer) ->
  CListProg v c ->
  IO ()
qcListProg1 numPrev m off minLen maxLen algo p =
  quickCheckWith (stdArgs {maxSuccess=1000}) ( \(l1 :: [Integer]) ->
        let l = (\x -> x `mod` m - off) <$> take (fromInteger maxLen) l1
            leftResult =
              ( interpretCListProgOnConInputs [fromInteger <$> l] (fromInteger . algo <$> inits l numPrev) p listAuxcfuncMap listCombcfuncMap :: Either VerificationConditions c
              )
            rightResult = Right $ fromInteger $ algo l
         in (length l < fromInteger numPrev || length l < fromInteger minLen || (leftResult == rightResult) || trace (show l) (trace (show leftResult) (trace (show rightResult) False))))
    where
      inits l numInits | numInits /= 0 = inits (init l) (numInits - 1) ++ [init l]
      inits _ _ = []

    