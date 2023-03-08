{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Component.IntermediateVarSet where

import Grisette

newtype IntermediateVarSet = IntermediateVarSet SymbolSet
  deriving (Show)
  deriving newtype (Semigroup, Monoid)

instance EvaluateSym IntermediateVarSet where
  evaluateSym _ _ = id

instance ExtractSymbolics IntermediateVarSet where
  extractSymbolics (IntermediateVarSet v) = v

instance Mergeable IntermediateVarSet where
  rootStrategy = SimpleStrategy mrgIte

instance SimpleMergeable IntermediateVarSet where
  mrgIte _ (IntermediateVarSet l) (IntermediateVarSet r) = IntermediateVarSet $ unionSet l r
