module Common.T where

import GHC.Generics
import Grisette
import Control.Monad.Except
import Data.Hashable

data CT ci
  = CBool Bool
  | CInt ci
  deriving (Show, Generic, Eq, Ord)
  deriving (ToCon (T si)) via (Default (CT ci))

data T si
  = TBool SymBool
  | TInt si
  deriving (Show, Generic, Eq, Hashable)
  deriving (Mergeable, ToSym (CT ci), ExtractSymbolics, SEq, EvaluateSym) via (Default (T si))

deriving via (Default (T s2)) instance ToSym s1 s2 => ToSym (T s1) (T s2)
deriving via (Default (T s2)) instance ToCon s1 s2 => ToCon (T s1) (T s2)

type MT si = UnionM (T si)

data TSpec
  = BoolValue
  | IntValue

instance (GenSymSimple () si, Mergeable si) => GenSym () (T si) where
  fresh () = do
    b <- simpleFresh ()
    i <- simpleFresh ()
    chooseFresh [TBool b, TInt i]

instance (GenSymSimple () si, Mergeable si) => GenSym TSpec (T si) where
  fresh BoolValue = do
    b <- simpleFresh ()
    return $ mrgReturn $ TBool b
  fresh IntValue = do
    i <- simpleFresh ()
    return $ mrgReturn $ TInt i

inputSpaceMT :: forall si. (Mergeable si) => ([[si]] -> SymBool) -> [[MT si]] -> SymBool
inputSpaceMT space inputs = simpleMerge $ do
  x <- go1 inputs
  case x of
    Nothing -> con False
    Just siss -> return $ space siss
  where
    go :: [MT si] -> UnionM (Maybe [si])
    go [] = mrgReturn $ Just []
    go (x:xs) = do
      r <- go xs
      v <- x
      case (r, v) of
        (Just r', TInt v') -> mrgReturn $ Just (v':r')
        _ -> mrgReturn Nothing
    go1 :: [[MT si]] -> UnionM (Maybe [[si]])
    go1 [] = mrgReturn $ Just []
    go1 (x:xs) = do
      r <- go1 xs
      v <- go x
      case (r, v) of
        (Just r', Just v') -> mrgReturn $ Just (v':r')
        _ -> mrgReturn Nothing

assumeInteger :: (Mergeable si) => MT si ->ExceptT VerificationConditions UnionM si
assumeInteger x = do
  x1 <- lift x
  case x1 of
    TBool _ -> mrgThrowError AssumptionViolation
    TInt si -> mrgReturn si

spec2Spec :: ([[SymInteger]]
            -> SymInteger -> ExceptT VerificationConditions UnionM SymBool)
           -> [[MT SymInteger]]
           -> MT SymInteger
           -> ExceptT VerificationConditions UnionM SymBool
spec2Spec spec input result = do
  integerInputs <- (mrgTraverse . mrgTraverse) assumeInteger input
  integerResult <- assumeInteger result
  spec integerInputs integerResult

spec2Spec' :: forall a. Mergeable a => ([[a]]
            -> ExceptT VerificationConditions UnionM a)
           -> [[MT a]]
           -> ExceptT VerificationConditions UnionM (MT a)
spec2Spec' spec input = do
  integerInputs <- (mrgTraverse . mrgTraverse) assumeInteger input
  r <- spec integerInputs
  mrgReturn $ mrgReturn $ TInt r

