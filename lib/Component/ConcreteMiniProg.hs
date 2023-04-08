module Component.ConcreteMiniProg where

import Common.Val
import Component.MiniProg
import Control.Monad.Except
import Data.List (sortBy)
import GHC.Generics
import Grisette
import Common.FuncMap

data CNode op cval = CNode op cval [cval]
  deriving (Generic, Show)

deriving via (Default (CNode op cval))
  instance (ToCon op op, ToCon val cval) => ToCon (Node op val) (CNode op cval)

data CMiniProg op cval = CMiniProg {cnodes :: [CNode op cval], output :: cval}
  deriving (Generic, Show)

-- deriving (ToCon (MiniProg val)) via (Default (CMiniProg cval))

instance (ToCon op op, ToCon val cval) => ToCon (MiniProg op val) (CMiniProg op cval) where
  toCon (MiniProg n o _) = do
    nc <- toCon n
    no <- toCon o
    return $ CMiniProg nc no

interpretCMiniProg :: (CValLike cval, MonadUnion m, Mergeable a, MonadError VerificationConditions m, FuncMapLike op a fm) =>
  [a] -> CMiniProg op cval -> fm -> m a
interpretCMiniProg inputs (CMiniProg ns o) fm = go [] s
  where
    s = sortBy (\(CNode _ r1 _) (CNode _ r2 _) -> compare r1 r2) ns
    go reg [] = mrgReturn $ getCVal inputs reg o
    go reg (CNode op _ nodeInputs : xs) = do
      r <- case getFunc op fm of Func _ _ f -> f $ getCVal inputs reg <$> nodeInputs
      go (reg ++ [r]) xs
