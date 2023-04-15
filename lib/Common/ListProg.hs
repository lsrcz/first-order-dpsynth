module Common.ListProg where

import Data.Hashable
import GHC.Generics
import Grisette

data CListProgVal ci
  = CLBool Bool
  | CLInt ci
  | CLIntList [ci]
  deriving (Show, Read, Generic, Eq, Ord)
  deriving (ToCon (ListProgVal si)) via (Default (CListProgVal ci))

data ListProgVal si
  = LBool SymBool
  | LInt si
  | LIntList [si]
  deriving (Show, Generic, Eq, Hashable)
  deriving
    ( Mergeable,
      ToSym (CListProgVal ci),
      ExtractSymbolics,
      SEq,
      EvaluateSym
    )
    via (Default (ListProgVal si))

type MListProgVal si = UnionM (ListProgVal si)

