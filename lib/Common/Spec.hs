module Common.Spec where

import Control.Monad.Except
import Data.Foldable
import Grisette

specV ::
  forall a e.
  (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  ([[a]] -> [Int] -> a) ->
  (Int -> [[Int]]) ->
  [[a]] ->
  a ->
  ExceptT VerificationConditions UnionM SymBool
specV apply allBitStrings inputs v =
  mrgReturn $
    foldl' (\acc x -> acc &&~ v >=~ x) (con True) t
      &&~ foldl' (\acc x -> acc ||~ v ==~ x) (con False) t
  where
    t = map (apply inputs) (allBitStrings (length $ head inputs))

safeSpecV ::
  forall a e.
  (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  ([[a]] -> [Int] -> ExceptT VerificationConditions UnionM a) ->
  (Int -> [[Int]]) ->
  [[a]] ->
  a ->
  ExceptT VerificationConditions UnionM SymBool
safeSpecV safeApply allBitStrings inputs v = do
  t1 <- t
  mrgReturn $
    foldl' (\acc x -> acc &&~ v >=~ x) (con True) t1
      &&~ foldl' (\acc x -> acc ||~ v ==~ x) (con False) t1
  where
    t = mrgTraverse (safeApply inputs) (allBitStrings (length $ head inputs))

spec ::
  forall a e.
  (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  ([[a]] -> [Int] -> a) ->
  (Int -> [[Int]]) ->
  [[a]] ->
  ExceptT VerificationConditions UnionM a
spec apply allBitStrings inputs =
  mrgReturn $
    foldl'
      ( \acc v ->
          let a = apply inputs v
           in mrgIte (a >=~ acc) a acc
      )
      0
      (allBitStrings (length $ head inputs))

safeSpec ::
  forall a e.
  (Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) =>
  ([[a]] -> [Int] -> ExceptT VerificationConditions UnionM a) ->
  (Int -> [[Int]]) ->
  [[a]] ->
  ExceptT VerificationConditions UnionM a
safeSpec safeApply allBitStrings inputs =
  foldM
    ( \acc v -> do
        a <- safeApply inputs v
        mrgReturn $ mrgIte (a >=~ acc) a acc
    )
    0
    (allBitStrings (length $ head inputs))
