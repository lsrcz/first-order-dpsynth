{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Component.ConcreteMiniProg where
import qualified Data.ByteString as B
import Component.MiniProg
import GHC.Generics
import Grisette
import Data.List (sortBy)
import qualified Data.HashMap.Strict as M
import Control.Monad.Except


data CVal
  = CInternal Int
  | CInput Int
  deriving (Generic, Show)
  deriving (ToCon Val) via (Default CVal)

data CNode = CNode B.ByteString Int [CVal]
  deriving (Generic, Show)
  deriving (ToCon Node) via (Default CNode)

data CMiniProg = CMiniProg { cnodes :: [CNode], output :: Int }
  deriving (Generic, Show)
  deriving (ToCon MiniProg) via (Default CMiniProg)

interpretCMiniProg :: (MonadUnion m, Mergeable a, MonadError VerificationConditions m) => [a] -> CMiniProg -> FuncMap a -> m a
interpretCMiniProg inputs (CMiniProg ns o) fm = go [] s
  where
    getOutputIdx (CNode _ r _) = r
    oidx = getOutputIdx (ns !! o)
    s = sortBy (\(CNode _ r1 _) (CNode _ r2 _) -> compare r1 r2) ns
    getNodeInputValue _ (CInput i) = inputs !! i
    getNodeInputValue reg (CInternal i) = reg !! i
    go reg [] = mrgReturn $ reg !! oidx
    go reg (CNode op _ nodeInputs:xs) = do
      r <- case fm M.! op of Func f -> f $ getNodeInputValue reg <$> nodeInputs
      go (reg ++ [r]) xs