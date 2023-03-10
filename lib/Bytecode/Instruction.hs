module Bytecode.Instruction where
import Grisette
import qualified Data.ByteString as B
import GHC.Generics
import Control.Monad.Except
import qualified Data.HashMap.Lazy as M
import Common.Val

type Op = B.ByteString

data Instruction = Instruction (UnionM Op) [UnionM Val] deriving (Show, Generic)
  deriving (Mergeable, EvaluateSym, ToSym CInstruction) via (Default Instruction)

data CInstruction = CInstruction Op [CVal]
  deriving (Generic, Show)
  deriving (ToCon Instruction) via (Default CInstruction)

data InstructionSpec = InstructionSpec {
  instructionOpSpec :: [Op],
  maxArgNum :: Int,
  inputNumSpec :: Int,
  instrPosSpec :: Int
}

instance GenSym InstructionSpec Instruction where
instance GenSymSimple InstructionSpec Instruction where
  simpleFresh (InstructionSpec ops narg ninput pinstr) = do
    op <- chooseFresh ops
    i <- simpleFresh (SimpleListSpec narg (ValSpec ninput pinstr))
    return $ Instruction op i

type Bytecode = [Instruction]

type CBytecode = [CInstruction]

data BytecodeSpec = BytecodeSpec {
  instrsBCSpec :: [([Op], Int)],
  inputNumBCSpec :: Int
}

data GroupedBytecodeSpec = GroupedBytecodeSpec {
  instrsGBCSpec :: [[([Op], Int)]],
  inputNumGBCSpec :: Int
}

instance GenSym BytecodeSpec Bytecode where
instance GenSymSimple BytecodeSpec Bytecode where
  simpleFresh (BytecodeSpec is n) =
    traverse (\((op, arg), pos) -> simpleFresh (InstructionSpec op arg n pos)) $
      zip is [0..]

instance GenSym GroupedBytecodeSpec Bytecode where
instance GenSymSimple GroupedBytecodeSpec Bytecode where
  simpleFresh (GroupedBytecodeSpec is numInputs) = go 0 is
    where
      go _ [] = return []
      go n (x:xs) = do
        h <- traverse (\(op, arg) -> simpleFresh (InstructionSpec op arg numInputs n)) x 
        r <- go (n + length x) xs
        return $ h ++ r

data Func a where
  Func :: (forall m. (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => [a] -> m a) -> Func a

instance Mergeable (Func a) where
  rootStrategy = SimpleStrategy mrgIte

instance SimpleMergeable (Func a) where
  mrgIte c (Func f) (Func g) = Func (\x -> mrgIf c (f x) (g x))

type FuncMap a = M.HashMap Op (Func a)

runFunc :: (MonadError VerificationConditions m, MonadUnion m, Mergeable a) => Func a -> [a] -> m a
runFunc (Func f) = f

getFunc :: Op -> FuncMap a -> Func a
getFunc = flip (M.!)

getFuncU :: UnionM Op -> FuncMap a -> Func a
getFuncU = (getFunc #~)

interpretInstruction ::
  forall m a. (MonadError VerificationConditions m, MonadUnion m, SimpleMergeable a) =>
    [a] -> [a] -> Instruction -> FuncMap a -> m a
interpretInstruction inputs memory (Instruction op l) fm = do
  args1 <- args
  runFunc func args1
  where
    getVal :: Val -> m a
    getVal (Input x) = do
      x1 <- liftToMonadUnion x
      mrgReturn $ inputs !! x1
    getVal (Internal x) = do
      x1 <- liftToMonadUnion x
      mrgReturn $ memory !! x1
    getValU x = liftToMonadUnion x >>= getVal
    func = getFuncU op fm
    args = mrgTraverse getValU l

interpretBytecode ::
  forall m a. (MonadError VerificationConditions m, MonadUnion m, SimpleMergeable a) =>
    [a] -> Bytecode -> FuncMap a -> m a
interpretBytecode inputs code fm = go inputs [] code
  where
    go :: [a] -> [a] -> Bytecode -> m a
    go _ m [] = mrgReturn $ last m
    go i m (ins:inss) = do
      r <- interpretInstruction i m ins fm
      go i (m ++ [r]) inss
