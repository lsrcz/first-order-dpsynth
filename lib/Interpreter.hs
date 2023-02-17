module Interpreter where

import Control.Monad.Except
import Core
import qualified Data.HashMap.Lazy as M
import Data.Hashable
import Grisette

interpretIntAST ::
  (Mergeable val, Eq val, Hashable val, SimpleMergeable val) =>
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  [val] ->
  AST val ->
  ExceptT VerificationConditions UnionM val
interpretIntAST u b args = htmemo go
  where
    go (Arg v) = mrgLift $ do
      vv <- v
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
    go (NoMrg x) = go #~ x

interpretSketch ::
  forall val.
  (Mergeable val, Eq val, Hashable val, SimpleMergeable val) =>
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  Program val ->
  [[val]] ->
  ExceptT VerificationConditions UnionM val
interpretSketch u b sk = go (inits sk)
  where
    go :: [val] -> [[val]] -> ExceptT VerificationConditions UnionM val
    go v [] = interpretIntAST u b v #~ terminate sk
    go v (a : as) = do
      r <-
        mrgTraverse
          (\(x :: UnionM (AST val)) -> interpretIntAST u b (a ++ v) #~ x)
          (updates sk)
      go r as
