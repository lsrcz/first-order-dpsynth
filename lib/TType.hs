module TType where
import Grisette
import GHC.Generics
import Core
import qualified Data.HashMap.Strict as M
import Control.Monad.Except
import Data.Hashable

data CT
  = CB Bool
  | CI Integer
  deriving (Generic, Show)
  deriving (ToCon T) via Default CT

data T
  = B SymBool
  | I SymInteger
  deriving (Generic, Hashable, Eq, Show)
  deriving (Mergeable, ToSym CT, ExtractSymbolics, SEq, EvaluateSym) via Default T

$(makeUnionWrapper "mrg" ''T)

type UT = UnionM T

unary :: (SymInteger -> SymInteger) -> UT -> ExceptT VerificationConditions UnionM UT
unary f u = do
  v <- lift u
  case v of
    B _ -> mrgThrowError AssumptionViolation
    I si -> mrgReturn $ mrgReturn $ I $ f si

availableUnaryT :: UnaryFuncMap (UnionM T)
availableUnaryT =
  M.fromList
    [ ("zero", unary (const 0)),
      ("-", unary negate),
      ("id", unary id)
    ]

binary :: (SymInteger -> SymInteger -> SymInteger) -> UT -> UT -> ExceptT VerificationConditions UnionM UT
binary f u1 u2 = do
  v1 <- lift u1
  v2 <- lift u2
  case (v1, v2) of
    (I si1, I si2) -> mrgReturn $ mrgReturn $ I $ f si1 si2
    _ -> mrgThrowError AssumptionViolation


availableBinaryT :: BinaryFuncMap UT
availableBinaryT =
  M.fromList
    [ ("+", binary (+)),
      ("-", binary (-)),
      ("-comp", binary $ flip (-)),
      ("max", binary $ \x y -> mrgIte (x >=~ y) x y),
      ("min", binary $ \x y -> mrgIte (x >=~ y) y x)
    ]

data TSpec = BoolVal | IntVal

instance GenSym TSpec T where
instance GenSymSimple TSpec T where
  simpleFresh BoolVal = B <$> simpleFresh ()
  simpleFresh IntVal = I <$> simpleFresh ()

utcmp :: (SymInteger -> SymInteger -> SymBool) -> UT -> UT -> ExceptT VerificationConditions UnionM SymBool
utcmp f u1 u2 = do
  v1 <- lift u1
  v2 <- lift u2
  case (v1, v2) of
    (I si1, I si2) -> mrgReturn $ f si1 si2
    _ -> mrgThrowError AssumptionViolation

utgeq :: UT -> UT -> ExceptT VerificationConditions UnionM SymBool
utgeq = utcmp (>=~)
uteq :: UT -> UT -> ExceptT VerificationConditions UnionM SymBool
uteq = utcmp (==~)



safeSpecVUT ::
  ([[UT]] -> [Int] -> ExceptT VerificationConditions UnionM UT) ->
  (Int -> [[Int]]) ->
  [[UT]] ->
  UT ->
  ExceptT VerificationConditions UnionM SymBool
safeSpecVUT safeApply allBitStrings inputs v = do
  t1 <- t
  --mrgReturn $
  r1 <- foldM (\acc x -> do
    r <- utgeq v x
    mrgReturn $ acc &&~ r) (con True) t1
  r2 <- foldM (\acc x -> do
    r <- uteq v x
    mrgReturn $ acc ||~ r) (con False) t1
  mrgReturn $ r1 &&~ r2
     -- &&~ foldl' (\acc x -> acc ||~ v ==~ x) (con False) t1
  where
    t = mrgTraverse (safeApply inputs) (allBitStrings (length inputs))
