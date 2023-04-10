{-# LANGUAGE UndecidableInstances #-}

module Component.Ops where

import Common.FuncMap
import Common.T
import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as M
import Grisette

unaryFunc :: (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => a -> m a) -> Func a
unaryFunc f = Func 1 False $ \case
  [a] -> f a
  _ -> mrgThrowError AssertionViolation

binaryFunc :: Bool -> (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => a -> a -> m a) -> Func a
binaryFunc comm f = Func 2 comm $ \case
  [a, b] -> f a b
  _ -> mrgThrowError AssertionViolation

unaryCFunc :: (a -> Either VerificationConditions a) -> CFunc a
unaryCFunc f = CFunc 1 False $ \case
  [a] -> f a
  _ -> throwError AssertionViolation

binaryCFunc :: Bool -> (a -> a -> Either VerificationConditions a) -> CFunc a
binaryCFunc comm f = CFunc 2 comm $ \case
  [a, b] -> f a b
  _ -> throwError AssertionViolation

symMax :: (SOrd a, SimpleMergeable a) => a -> a -> a
symMax l r = mrgIte (l >=~ r) l r

symMin :: (SOrd a, SimpleMergeable a) => a -> a -> a
symMin l r = mrgIte (l >=~ r) r l

funcMap :: (Num a, SOrd a, SimpleMergeable a) => M.HashMap B.ByteString (Func a)
funcMap =
  M.fromList
    [ ("id", unaryFunc mrgReturn),
      ("zero", unaryFunc (const $ mrgReturn 0)),
      ("negate", unaryFunc $ mrgReturn . negate),
      ("+", binaryFunc True $ \l r -> mrgReturn $ l + r),
      ("-", binaryFunc False $ \l r -> mrgReturn $ l - r),
      ("max", binaryFunc True $ \l r -> mrgReturn $ symMax l r),
      ("min", binaryFunc True $ \l r -> mrgReturn $ symMin l r)
    ]

cfuncMap :: (Num a, Ord a) => M.HashMap B.ByteString (CFunc a)
cfuncMap =
  M.fromList
    [ ("id", unaryCFunc return),
      ("zero", unaryCFunc (const $ return 0)),
      ("negate", unaryCFunc $ return . negate),
      ("+", binaryCFunc True $ \l r -> return $ l + r),
      ("-", binaryCFunc False $ \l r -> return $ l - r),
      ("max", binaryCFunc True $ \l r -> return $ max l r),
      ("min", binaryCFunc True $ \l r -> return $ min l r)
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

mtIntUnaryCFunc :: (ci -> Either VerificationConditions ci) -> CFunc (CT ci)
mtIntUnaryCFunc f = CFunc 1 False $ \case
  [a] -> do
    case a of
      CBool _ -> throwError AssertionViolation
      CInt si -> CInt <$> f si
  _ -> throwError AssertionViolation

mtIntBinaryCFunc :: Bool -> (ci -> ci -> Either VerificationConditions ci) -> CFunc (CT ci)
mtIntBinaryCFunc comm f = CFunc 2 comm $ \case
  [a, b] -> do
    case (a, b) of
      (CInt sa, CInt sb) -> CInt <$> f sa sb
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

mtInt2BoolBinaryCFunc :: Bool -> (ci -> ci -> Either VerificationConditions Bool) -> CFunc (CT ci)
mtInt2BoolBinaryCFunc comm f = CFunc 2 comm $ \case
  [a, b] -> do
    case (a, b) of
      (CInt sa, CInt sb) -> CBool <$> f sa sb
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

mtBoolBinaryCFunc :: Bool -> (Bool -> Bool -> Either VerificationConditions Bool) -> CFunc (CT si)
mtBoolBinaryCFunc comm f = CFunc 2 comm $ \case
  [a, b] -> do
    case (a, b) of
      (CBool sa, CBool sb) -> CBool <$> f sa sb
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

mtfuncMap :: (Num a, SOrd a, SimpleMergeable a) => M.HashMap B.ByteString (Func (MT a))
mtfuncMap =
  M.fromList
    [ ("id", mtIntUnaryFunc mrgReturn),
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

mtcfuncMap :: (Num a, Ord a) => M.HashMap B.ByteString (CFunc (CT a))
mtcfuncMap =
  M.fromList
    [ ("id", mtIntUnaryCFunc return),
      ("zero", mtIntUnaryCFunc (const $ return 0)),
      ("negate", mtIntUnaryCFunc $ return . negate),
      ("+", mtIntBinaryCFunc True $ \l r -> return $ l + r),
      ("-", mtIntBinaryCFunc False $ \l r -> return $ l - r),
      ("max", mtIntBinaryCFunc True $ \l r -> return $ max l r),
      ("min", mtIntBinaryCFunc True $ \l r -> return $ min r l),
      ("<", mtInt2BoolBinaryCFunc False $ \l r -> return $ l < r),
      ("<=", mtInt2BoolBinaryCFunc False $ \l r -> return $ l <= r),
      ("&&", mtBoolBinaryCFunc True $ \l r -> return $ l && r),
      ("||", mtBoolBinaryCFunc True $ \l r -> return $ l || r)
    ]
