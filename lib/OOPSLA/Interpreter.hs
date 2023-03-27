module OOPSLA.Interpreter where

import Control.Monad.Except
import qualified Data.HashMap.Lazy as M
import Data.Hashable
import Grisette
import OOPSLA.Core

interpretIntAST ::
  (Show val, Mergeable val, Eq val, Hashable val, SimpleMergeable val) =>
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  TernaryFuncMap val ->
  [val] ->
  AST val ->
  ExceptT VerificationConditions UnionM val
interpretIntAST u b t args = htmemo go
  where
    go (Arg v) = mrgLift $ do
      vv <- v
      {-(if length args <= vv then trace (show args) $ trace (show vv) $ undefined else id) $-}
      mrgReturn $ args !! vv
    go (Const v) = mrgLift v
    go (Unary f sub) = do
      v <- go #~ sub
      f1 <- lift f
      (u M.! f1) v
    go (Binary f l r) = do
      lv <- go #~ l
      rv <- go #~ r
      f1 <- lift f
      (b M.! f1) lv rv
    go (Ternary f x y z) = do
      xv <- go #~ x
      yv <- go #~ y
      zv <- go #~ z
      f1 <- lift f
      (t M.! f1) xv yv zv
    go (NoMrg x) = go #~ x

interpretSketch ::
  forall val.
  (Show val, Mergeable val, Eq val, Hashable val, SimpleMergeable val) =>
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  TernaryFuncMap val ->
  Program val ->
  [[val]] ->
  ExceptT VerificationConditions UnionM val
interpretSketch u b t sk = go (inits sk)
  where
    go :: [val] -> [[val]] -> ExceptT VerificationConditions UnionM val
    go v (x : _) | null x = interpretIntAST u b t v #~ terminate sk
    go v l = do
      r <-
        mrgTraverse
          (\(x :: UnionM (AST val)) -> interpretIntAST u b t ((head <$> l) ++ v) #~ x)
          (updates sk)
      go r (tail <$> l)
