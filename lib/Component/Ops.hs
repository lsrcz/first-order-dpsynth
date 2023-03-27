module Component.Ops where

import Component.MiniProg
import Control.Monad.Except
import qualified Data.HashMap.Strict as M
import Grisette
import Common.T

unaryFunc :: (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => a -> m a) -> Func a
unaryFunc f = Func 1 False $ \case
  [a] -> f a
  _ -> mrgThrowError AssertionViolation

binaryFunc :: Bool -> (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => a -> a -> m a) -> Func a
binaryFunc comm f = Func 2 comm $ \case
  [a, b] -> f a b
  _ -> mrgThrowError AssertionViolation

funcMap :: (Num a, SOrd a, SimpleMergeable a) => FuncMap a
funcMap =
  M.fromList
    [ ("id", unaryFunc mrgReturn),
      ("zero", unaryFunc (const $ mrgReturn 0)),
      ("negate", unaryFunc $ mrgReturn . negate),
      ("+", binaryFunc True $ \l r -> mrgReturn $ l + r),
      ("-", binaryFunc False $ \l r -> mrgReturn $ l - r),
      ("max", binaryFunc True $ \l r -> mrgReturn $ mrgIte (l >=~ r) l r),
      ("min", binaryFunc True $ \l r -> mrgReturn $ mrgIte (l >=~ r) r l)
    ]

mtIntUnaryFunc :: Mergeable si => (forall m. (MonadError VerificationConditions m, MonadUnion m) => si -> m si) -> Func (MT si)
mtIntUnaryFunc f = Func 1 False $ \case
  [a] -> do
    r <- liftToMonadUnion a
    case r of
      TBool _ -> mrgThrowError AssertionViolation
      TInt si -> mrgFmap (mrgReturn . TInt) $ f si
  _ -> mrgThrowError AssertionViolation

mtIntBinaryFunc :: Mergeable si => Bool -> (forall m. (MonadError VerificationConditions m, MonadUnion m) => si -> si -> m si) -> Func (MT si)
mtIntBinaryFunc comm f = Func 2 comm $ \case
  [a, b] -> do
    ra <- liftToMonadUnion a
    rb <- liftToMonadUnion b
    case (ra, rb) of
      (TInt sa, TInt sb) -> mrgFmap (mrgReturn . TInt) $ f sa sb
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

mtInt2BoolBinaryFunc :: Mergeable si => Bool -> (forall m. (MonadError VerificationConditions m, MonadUnion m) => si -> si -> m SymBool) -> Func (MT si)
mtInt2BoolBinaryFunc comm f = Func 2 comm $ \case
  [a, b] -> do
    ra <- liftToMonadUnion a
    rb <- liftToMonadUnion b
    case (ra, rb) of
      (TInt sa, TInt sb) -> mrgFmap (mrgReturn . TBool) $ f sa sb
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

mtBoolBinaryFunc :: Mergeable si => Bool -> (forall m. (MonadError VerificationConditions m, MonadUnion m) => SymBool -> SymBool -> m SymBool) -> Func (MT si)
mtBoolBinaryFunc comm f = Func 2 comm $ \case
  [a, b] -> do
    ra <- liftToMonadUnion a
    rb <- liftToMonadUnion b
    case (ra, rb) of
      (TBool sa, TBool sb) -> mrgFmap (mrgReturn . TBool) $ f sa sb
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

mtfuncMap :: (Num a, SOrd a, SimpleMergeable a) => FuncMap (MT a)
mtfuncMap =
  M.fromList
    [ ("id", mtIntUnaryFunc mrgReturn ),
      ("zero", mtIntUnaryFunc (const $ mrgReturn 0)),
      ("negate", mtIntUnaryFunc $ mrgReturn . negate),
      ("+", mtIntBinaryFunc True $ \l r -> mrgReturn $ l + r),
      ("-", mtIntBinaryFunc False $ \l r -> mrgReturn $ l - r),
      ("max", mtIntBinaryFunc True $ \l r -> mrgReturn $ mrgIte (l >=~ r) l r),
      ("min", mtIntBinaryFunc True $ \l r -> mrgReturn $ mrgIte (l >=~ r) r l),
      ("<", mtInt2BoolBinaryFunc False $ \l r -> mrgReturn $ l <~ r),
      ("<=", mtInt2BoolBinaryFunc False $ \l r -> mrgReturn $ l <=~ r),
      ("&&", mtBoolBinaryFunc True $ \l r -> mrgReturn $ l &&~ r),
      ("||", mtBoolBinaryFunc True $ \l r -> mrgReturn $ l ||~ r)
      ]