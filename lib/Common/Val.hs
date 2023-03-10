module Common.Val where
import Grisette
import GHC.Generics

data Val
  = Internal (UnionM Int)
  | Input (UnionM Int)
  deriving (Generic, Show)
  deriving (Mergeable, SEq, EvaluateSym, ToSym CVal) via (Default Val)

data ValSpec = ValSpec { valInputNum :: Int, valInternalNum :: Int}

data CVal
  = CInternal Int
  | CInput Int
  deriving (Generic, Show)
  deriving (ToCon Val) via (Default CVal)

instance GenSym ValSpec Val where
  fresh (ValSpec ninput ninternal)
    | ninternal <= 0 = do
      i <- fresh (EnumGenBound 0 ninput)
      return $ mrgReturn $ Input i
    | otherwise = do
      inputs <- fresh (EnumGenBound 0 ninput)
      internals <- fresh (EnumGenBound 0 ninternal)
      chooseFresh [Internal internals, Input inputs]

