module Common.FuncMap where
import Control.Monad.Except
import Grisette
import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as M
import Data.Hashable

data Func a where
  Func :: Int -> Bool ->
    (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => [a] -> m a) -> Func a

class FuncMapLike op a fm | fm -> op a where
  getFuncMaybe :: op -> fm -> Maybe (Func a)
  getFunc :: op -> fm -> Func a

instance FuncMapLike B.ByteString a (M.HashMap B.ByteString (Func a)) where
  getFuncMaybe = M.lookup
  getFunc = flip (M.!)

class (Ord g, Hashable g, ToCon op op, Show op, EvaluateSym op) => OpCode op g | op -> g where
  opGroup :: op -> g

instance OpCode B.ByteString B.ByteString where
  opGroup = id