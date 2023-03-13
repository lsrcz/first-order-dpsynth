module Component.Ops where

import Component.MiniProg
import Control.Monad.Except
import qualified Data.HashMap.Strict as M
import Grisette

unaryFunc :: (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => a -> m a) -> Func a
unaryFunc f = Func $ \case
  [a] -> f a
  _ -> mrgThrowError AssertionViolation

binaryFunc :: (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => a -> a -> m a) -> Func a
binaryFunc f = Func $ \case
  [a, b] -> f a b
  _ -> mrgThrowError AssertionViolation

funcMap :: (Num a, SOrd a, SimpleMergeable a) => FuncMap a
funcMap =
  M.fromList
    [ ("id", unaryFunc mrgReturn),
      ("zero", unaryFunc (const $ mrgReturn 0)),
      ("negate", unaryFunc $ mrgReturn . negate),
      ("+", binaryFunc $ \l r -> mrgReturn $ l + r),
      ("-", binaryFunc $ \l r -> mrgReturn $ l - r),
      ("max", binaryFunc $ \l r -> mrgReturn $ mrgIte (l >=~ r) l r),
      ("min", binaryFunc $ \l r -> mrgReturn $ mrgIte (l >=~ r) r l)
    ]
