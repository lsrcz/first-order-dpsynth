module Bytecode.Prog where
import Bytecode.Instruction
import GHC.Generics
import Grisette
import Control.Monad.Except

data BytecodeProg a = BytecodeProg [a] [Bytecode] Bytecode
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (BytecodeProg a))

data CBytecodeProg a = CBytecodeProg [a] [CBytecode] CBytecode
  deriving (Show, Generic)

deriving via (Default (CBytecodeProg c))
  instance ToCon s c => ToCon (BytecodeProg s) (CBytecodeProg c)

deriving via (Default (BytecodeProg s))
  instance ToSym c s => ToSym (CBytecodeProg c) (BytecodeProg s) 

data BytecodeProgSpec spec = BytecodeProgSpec spec [BytecodeSpec] BytecodeSpec

data GroupedBytecodeProgSpec spec = GroupedBytecodeProgSpec spec [GroupedBytecodeSpec] GroupedBytecodeSpec

instance GenSymSimple spec a => GenSymSimple (BytecodeProgSpec spec) (BytecodeProg a) where
  simpleFresh (BytecodeProgSpec s b f) = do
    inits <- traverse (const $ simpleFresh s) [0..length b - 1]
    updates <- traverse simpleFresh b
    final <- simpleFresh f
    return $ BytecodeProg inits updates final

instance GenSymSimple spec a => GenSymSimple (GroupedBytecodeProgSpec spec) (BytecodeProg a) where
  simpleFresh (GroupedBytecodeProgSpec s b f) = do
    inits <- traverse (const $ simpleFresh s) [0..length b - 1]
    updates <- traverse simpleFresh b
    final <- simpleFresh f
    return $ BytecodeProg inits updates final

interpretBytecodeProg ::
  forall m a. (MonadError VerificationConditions m, MonadUnion m, SimpleMergeable a) =>
  [[a]] -> BytecodeProg a -> FuncMap a -> m a
interpretBytecodeProg inputs (BytecodeProg inits codes finalcode) fm = do
  finalIntermediate <- go inputs inits
  interpretBytecode finalIntermediate finalcode fm
  where
    go ([]:_) currIntermediate = mrgReturn currIntermediate
    go currInputs currIntermediate = do
      nextIntermediate <- mrgTraverse (go1 currInputs currIntermediate) codes
      go (tail <$> currInputs) nextIntermediate

    go1 :: [[a]] -> [a] -> Bytecode -> m a
    go1 currInputs currIntermediate code =
      interpretBytecode ((head <$> currInputs) ++ currIntermediate) code fm
