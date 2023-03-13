module Common.Val where
import Grisette
import GHC.Generics
import Control.Monad.Except
import GHC.TypeLits

data Val
  = Input (UnionM Int)
  | Internal (UnionM Int)
  deriving (Generic, Show)
  deriving (Mergeable, SEq, SOrd, EvaluateSym, ToSym CVal) via (Default Val)

data ValSpec = ValSpec { valInputNum :: Int, valInternalNum :: Int}

data CVal
  = CInput Int
  | CInternal Int
  deriving (Generic, Show, Eq, Ord)
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
  leVal :: v -> v -> SymBool
  inputVal :: Int -> v
  internalVal :: Int -> Int -> v
  getVal :: (MonadUnion m, MonadError VerificationConditions m, Mergeable l) => [l] -> [l] -> v -> m l
  boundVal :: v -> v -> v -> SymBool
  boundVal l r v = leVal l v &&~ ltVal v r

instance ValLike Val where
  eqVal = (==~)
  ltVal = (<~)
  leVal = (<=~)
  inputVal v = Input $ mrgSingle v
  internalVal _ v = Internal $ mrgSingle v
  getVal inputs internals v = case v of
    Input i -> liftToMonadUnion i >>= gi inputs
    Internal i -> liftToMonadUnion i >>= gi internals
    where
      gi l r | r < length l = mrgReturn (l !! r)
      gi _ _ = throwError AssertionViolation 

instance (ValLike v, Mergeable v) => ValLike (UnionM v) where
  eqVal l r = simpleMerge $ do
    l1 <- l
    eqVal l1 <$> r
  ltVal l r = simpleMerge $ do
    l1 <- l
    ltVal l1 <$> r
  leVal l r = simpleMerge $ do
    l1 <- l
    leVal l1 <$> r
  inputVal v = mrgSingle $ inputVal v
  internalVal numInputs v = mrgSingle $ internalVal numInputs v
  getVal inputs internals v = liftToMonadUnion v >>= getVal inputs internals

class Ord v => CValLike v where
  getCVal :: [l] -> [l] -> v -> l

instance CValLike CVal where
  getCVal inputs _ (CInput i) = inputs !! i
  getCVal _ reg (CInternal i) = reg !! i

instance ValLike SymInteger where
  eqVal = (==~)
  ltVal = (<~)
  leVal = (<=~)
  inputVal = fromIntegral
  internalVal numInputs v = fromIntegral $ numInputs + v
  getVal = go 0
    where
      go _ [] [] _ = undefined
      go _ [] [x] _ = mrgReturn x
      go n [] (x:xs) v = mrgIf (eqVal n v) (mrgReturn x) (go (n + 1) [] xs v)
      go _ [x] [] _ = mrgReturn x
      go n [x] internals' v = mrgIf (eqVal n v) (mrgReturn x) (go (n + 1) [] internals' v)
      go n (x:xs) internals' v = mrgIf (eqVal n v) (mrgReturn x) (go (n + 1) xs internals' v)

instance CValLike Integer where
  getCVal inputs reg i = (inputs ++ reg) !! fromIntegral i

instance (KnownNat n, 1 <= n) => ValLike (SymIntN n) where
  eqVal = (==~)
  ltVal = (<~)
  leVal = (<=~)
  inputVal = fromIntegral
  internalVal numInputs v = fromIntegral $ numInputs + v
  getVal = go 0
    where
      go _ [] [] _ = undefined
      go _ [] [x] _ = mrgReturn x
      go n [] (x:xs) v = mrgIf (eqVal n v) (mrgReturn x) (go (n + 1) [] xs v)
      go _ [x] [] _ = mrgReturn x
      go n [x] internals' v = mrgIf (eqVal n v) (mrgReturn x) (go (n + 1) [] internals' v)
      go n (x:xs) internals' v = mrgIf (eqVal n v) (mrgReturn x) (go (n + 1) xs internals' v)

instance (KnownNat n, 1 <= n) => CValLike (IntN n) where
  getCVal inputs reg i = (inputs ++ reg) !! fromIntegral i

