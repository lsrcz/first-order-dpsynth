module OOPSLA.Ops where

import Common.T
import Control.Monad.Except
import qualified Data.HashMap.Strict as M
import Grisette
import OOPSLA.Core

availableUnary :: (Num a, SimpleMergeable a) => UnaryFuncMap a
availableUnary =
  M.fromList
    [ ("zero", const $ mrgReturn 0),
      ("-", mrgReturn . negate),
      ("id", mrgReturn)
    ]

availableBinary :: (Num a, SOrd a, SimpleMergeable a) => BinaryFuncMap a
availableBinary =
  M.fromList
    [ ("+", \x y -> mrgReturn $ x + y),
      ("-", \x y -> mrgReturn $ x - y),
      ("-comp", \x y -> mrgReturn $ y - x),
      ("max", \x y -> mrgReturn $ mrgIte (x >=~ y :: SymBool) x y),
      ("min", \x y -> mrgReturn $ mrgIte (x >=~ y :: SymBool) y x)
    ]

availableTernary :: (Num a, SOrd a, SimpleMergeable a) => TernaryFuncMap a
availableTernary = M.fromList []

noOverflowAvailableBinary :: (Num a, SOrd a, SimpleMergeable a) => BinaryFuncMap a
noOverflowAvailableBinary =
  M.fromList
    [ ( "+",
        \x y -> do
          let r = x + y
          symAssume $ (x >~ 0 &&~ y >~ 0) `implies` (r >~ 0)
          symAssume $ (x <~ 0 &&~ y <~ 0) `implies` (r <~ 0)
          mrgReturn r
      ),
      ( "-",
        \x y -> do
          let r = x - y
          symAssume $ (x >~ 0 &&~ y <~ 0) `implies` (r >~ 0)
          symAssume $ (x <~ 0 &&~ y >~ 0) `implies` (r <~ 0)
          mrgReturn r
      ),
      ( "-comp",
        \x y -> do
          let r = y - x
          symAssume $ (x >~ 0 &&~ y <~ 0) `implies` (r <~ 0)
          symAssume $ (x <~ 0 &&~ y >~ 0) `implies` (r >~ 0)
          mrgReturn r
      ),
      ( "max",
        \x y -> do
          let r = mrgIte (x >=~ y :: SymBool) x y
          symAssume $ r >=~ x
          symAssume $ r >=~ y
          mrgReturn r
      ),
      ( "min",
        \x y -> do
          let r = mrgIte (x >=~ y :: SymBool) y x
          symAssume $ r <=~ x
          symAssume $ r <=~ y
          mrgReturn r
      )
    ]

type EM si = ExceptT VerificationConditions UnionM si

mtIntUnaryFunc :: Mergeable si => (si -> EM si) -> MT si -> EM (MT si)
mtIntUnaryFunc f a = do
  r <- liftToMonadUnion a
  case r of
    TBool _ -> mrgThrowError AssertionViolation
    TInt si -> mrgFmap (mrgReturn . TInt) $ f si

mtIntBinaryFunc :: Mergeable si => (si -> si -> EM si) -> MT si -> MT si -> EM (MT si)
mtIntBinaryFunc f a b = do
  ra <- liftToMonadUnion a
  rb <- liftToMonadUnion b
  case (ra, rb) of
    (TInt sa, TInt sb) -> mrgFmap (mrgReturn . TInt) $ f sa sb
    _ -> mrgThrowError AssertionViolation

mtInt2BoolBinaryFunc :: Mergeable si => (si -> si -> EM SymBool) -> MT si -> MT si -> EM (MT si)
mtInt2BoolBinaryFunc f a b = do
  ra <- liftToMonadUnion a
  rb <- liftToMonadUnion b
  case (ra, rb) of
    (TInt sa, TInt sb) -> mrgFmap (mrgReturn . TBool) $ f sa sb
    _ -> mrgThrowError AssertionViolation

mtBoolBinaryFunc :: Mergeable si => (SymBool -> SymBool -> EM SymBool) -> MT si -> MT si -> EM (MT si)
mtBoolBinaryFunc f a b = do
  ra <- liftToMonadUnion a
  rb <- liftToMonadUnion b
  case (ra, rb) of
    (TBool sa, TBool sb) -> mrgFmap (mrgReturn . TBool) $ f sa sb
    _ -> mrgThrowError AssertionViolation

mtAvailableUnary :: (Num a, SimpleMergeable a) => UnaryFuncMap (MT a)
mtAvailableUnary =
  M.fromList
    [ ("zero", mtIntUnaryFunc $ const $ mrgReturn 0),
      ("one", mtIntUnaryFunc $ const $ mrgReturn 1),
      ("-", mtIntUnaryFunc $ mrgReturn . negate),
      ("id", mtIntUnaryFunc mrgReturn)
    ]

mtAvailableBinary :: (Num a, SOrd a, SimpleMergeable a) => BinaryFuncMap (MT a)
mtAvailableBinary =
  M.fromList
    [ ("+", mtIntBinaryFunc $ \x y -> mrgReturn $ x + y),
      ("-", mtIntBinaryFunc $ \x y -> mrgReturn $ x - y),
      ("-comp", mtIntBinaryFunc $ \x y -> mrgReturn $ y - x),
      ("max", mtIntBinaryFunc $ \x y -> mrgReturn $ mrgIte (x >=~ y :: SymBool) x y),
      ("min", mtIntBinaryFunc $ \x y -> mrgReturn $ mrgIte (x >=~ y :: SymBool) y x),
      ("<", mtInt2BoolBinaryFunc $ \x y -> mrgReturn $ x <~ y),
      ("<=", mtInt2BoolBinaryFunc $ \x y -> mrgReturn $ x <=~ y),
      (">", mtInt2BoolBinaryFunc $ \x y -> mrgReturn $ x >~ y),
      (">=", mtInt2BoolBinaryFunc $ \x y -> mrgReturn $ x >=~ y),
      ("&&", mtBoolBinaryFunc $ \x y -> mrgReturn $ x &&~ y),
      ("||", mtBoolBinaryFunc $ \x y -> mrgReturn $ x ||~ y)
    ]

mtAvailableTernary :: (Num a, SOrd a, SimpleMergeable a) => TernaryFuncMap (MT a)
mtAvailableTernary = M.fromList [
  ("ite", \c a b -> do
    rc <- liftToMonadUnion c
    case rc of
      TBool sc -> mrgReturn $ mrgIte sc a b
      _ -> mrgThrowError AssertionViolation)
  ]
