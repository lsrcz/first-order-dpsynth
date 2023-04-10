module Component.ConcreteMiniProg where

import Common.Val
import Component.MiniProg
import Data.List (sortBy)
import GHC.Generics
import Grisette
import Common.FuncMap
import Control.Monad.Except

data CNode op cval = CNode op cval [cval]
  deriving (Generic, Show)

deriving via (Default (CNode cop cval))
  instance (ToCon op cop, ToCon val cval) => ToCon (Node op val) (CNode cop cval)

data CMiniProg op cval = CMiniProg {cnodes :: [CNode op cval], output :: cval}
  deriving (Generic, Show)

-- deriving (ToCon (MiniProg val)) via (Default (CMiniProg cval))

instance (ToCon op cop, ToCon val cval) => ToCon (MiniProg op val) (CMiniProg cop cval) where
  toCon (MiniProg n o _) = do
    nc <- toCon n
    no <- toCon o
    return $ CMiniProg nc no

interpretCMiniProgOnSymInputs :: (CValLike cval, MonadUnion m, Mergeable a, MonadError VerificationConditions m, MonadFresh m, FuncMapLike op a fm) =>
  [a] -> CMiniProg op cval -> fm -> m a
interpretCMiniProgOnSymInputs inputs (CMiniProg ns o) fm = go [] s
  where
    s = sortBy (\(CNode _ r1 _) (CNode _ r2 _) -> compare r1 r2) ns
    go reg [] = return $ getCVal inputs reg o
    go reg (CNode op _ nodeInputs : xs) = do
      r <- case getFunc op fm of Func _ _ f -> f $ getCVal inputs reg <$> nodeInputs
      go (reg ++ [r]) xs

interpretCMiniProgOnConInputs :: (CValLike cval, CFuncMapLike op c fm) =>
  [c] -> CMiniProg op cval -> fm -> Either VerificationConditions c
interpretCMiniProgOnConInputs inputs (CMiniProg ns o) fm = go [] s
  where
    s = sortBy (\(CNode _ r1 _) (CNode _ r2 _) -> compare r1 r2) ns
    go reg [] = return $ getCVal inputs reg o
    go reg (CNode op _ nodeInputs : xs) = do
      r <- case getCFunc op fm of CFunc _ _ f -> f $ getCVal inputs reg <$> nodeInputs
      go (reg ++ [r]) xs

