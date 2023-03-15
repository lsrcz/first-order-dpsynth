module Component.ConcreteMiniProg where

import Common.Val
import Component.MiniProg
import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as M
import Data.List (sortBy)
import GHC.Generics
import Grisette

data CNode cval = CNode B.ByteString cval [cval]
  deriving (Generic, Show)
  deriving (ToCon (Node val)) via (Default (CNode cval))

data CMiniProg cval = CMiniProg {cnodes :: [CNode cval], output :: cval}
  deriving (Generic, Show)
  deriving (ToCon (MiniProg val)) via (Default (CMiniProg cval))

interpretCMiniProg :: (CValLike cval, MonadUnion m, Mergeable a, MonadError VerificationConditions m) => [a] -> CMiniProg cval -> FuncMap a -> m a
interpretCMiniProg inputs (CMiniProg ns o) fm = go [] s
  where
    s = sortBy (\(CNode _ r1 _) (CNode _ r2 _) -> compare r1 r2) ns
    go reg [] = mrgReturn $ getCVal inputs reg o
    go reg (CNode op _ nodeInputs : xs) = do
      r <- case fm M.! op of Func _ _ f -> f $ getCVal inputs reg <$> nodeInputs
      go (reg ++ [r]) xs
