module Bytecode.Ops where

import Bytecode.Instruction
import Control.Monad.Except
import qualified Data.HashMap.Strict as M
import Grisette

bytecodeUnaryFunc :: (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => a -> m a) -> Func a
bytecodeUnaryFunc f = Func $ \case
  [] -> mrgThrowError AssertionViolation
  (a:_) -> f a

bytecodeBinaryFunc :: (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => a -> a -> m a) -> Func a
bytecodeBinaryFunc f = Func $ \case
  [] -> mrgThrowError AssertionViolation
  [_] -> mrgThrowError AssertionViolation
  (a: b:_) -> f a b

bytecodeFuncMap :: (Num a, SOrd a, SimpleMergeable a) => FuncMap a
bytecodeFuncMap =
  M.fromList
    [ ("id", bytecodeUnaryFunc mrgReturn),
      ("negate", bytecodeUnaryFunc $ mrgReturn . negate),
      ("+", bytecodeBinaryFunc $ \l r -> mrgReturn $ l + r),
      ("-", bytecodeBinaryFunc $ \l r -> mrgReturn $ l - r),
      ("max", bytecodeBinaryFunc $ \l r -> mrgReturn $ mrgIte (l >=~ r) l r),
      ("min", bytecodeBinaryFunc $ \l r -> mrgReturn $ mrgIte (l >=~ r) r l)
    ]

