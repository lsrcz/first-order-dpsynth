module Component.ConcreteProg where
import Component.ConcreteMiniProg
import Grisette
import Control.Monad.Except
import Component.MiniProg
import GHC.Generics
import Component.Prog

data CProg a = CProg [a] [CMiniProg] CMiniProg deriving (Generic, Show)

deriving via (Default (CProg c)) instance ToCon a c => ToCon (Prog a) (CProg c)

interpretCProg :: forall m c a. (ToSym c a, MonadUnion m, Mergeable a, MonadError VerificationConditions m) =>
  [[a]] -> CProg c -> FuncMap a -> m a
interpretCProg inputs (CProg inits progs finalprog) fm = do
  r <- go inputs (toSym <$> inits) progs
  interpretCMiniProg r finalprog fm
  where
    go :: [[a]] -> [a] -> [CMiniProg] -> m [a]
    go currInputs currIntermediates _ | null (head currInputs) = mrgReturn currIntermediates
    go currInputs currIntermediates miniprogs = do
      r <- go1 ((head <$> currInputs) ++ currIntermediates) miniprogs
      go (tail <$> currInputs) r miniprogs
    go1 :: [a] -> [CMiniProg] -> m [a]
    go1 i = mrgTraverse (\p -> interpretCMiniProg i p fm)
