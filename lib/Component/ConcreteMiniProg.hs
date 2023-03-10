module Component.ConcreteMiniProg where

import Component.MiniProg
import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as M
import Data.List (sortBy)
import GHC.Generics
import Grisette
import Common.Val

data CNode = CNode B.ByteString CVal [CVal]
  deriving (Generic, Show)
  deriving (ToCon Node) via (Default CNode)

data CMiniProg = CMiniProg {cnodes :: [CNode], output :: CVal}
  deriving (Generic, Show)
  deriving (ToCon MiniProg) via (Default CMiniProg)

interpretCMiniProg :: (MonadUnion m, Mergeable a, MonadError VerificationConditions m) => [a] -> CMiniProg -> FuncMap a -> m a
interpretCMiniProg inputs (CMiniProg ns o) fm = go [] s
  where
    s = sortBy (\(CNode _ (CInternal r1) _) (CNode _ (CInternal r2) _) -> compare r1 r2) ns
    getNodeInputValue _ (CInput i) = inputs !! i
    getNodeInputValue reg (CInternal i) = reg !! i
    go reg [] = mrgReturn $ getNodeInputValue reg o
    go reg (CNode op _ nodeInputs : xs) = do
      r <- case fm M.! op of Func f -> f $ getNodeInputValue reg <$> nodeInputs
      go (reg ++ [r]) xs
