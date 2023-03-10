module Common.Val where
import Grisette
import GHC.Generics
import Control.Monad.Except

data Val
  = Input (UnionM Int)
  | Internal (UnionM Int)
  deriving (Generic, Show)
  deriving (Mergeable, SEq, SOrd, EvaluateSym, ToSym CVal) via (Default Val)

data ValSpec = ValSpec { valInputNum :: Int, valInternalNum :: Int}

data CVal
  = CInput Int
  | CInternal Int
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
      chooseFresh [Input inputs, Internal internals]

newtype ChooseSpec l = ChooseSpec [l]

instance Mergeable l => GenSym (ChooseSpec l) l where
  fresh (ChooseSpec l) = chooseFresh l

class ValLike v where
  eqVal :: v -> v -> SymBool
  ltVal :: v -> v -> SymBool

instance ValLike Val where
  eqVal = (==~)
  ltVal = (<~)

instance ValLike v => ValLike (UnionM v) where
  eqVal l r = simpleMerge $ do
    l1 <- l
    eqVal l1 <$> r
  ltVal l r = simpleMerge $ do
    l1 <- l
    ltVal l1 <$> r
