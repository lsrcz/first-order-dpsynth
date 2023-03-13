module Bytecode where
import Bytecode.Prog
import Grisette
import Bytecode.Instruction
import Control.Monad.Except
import Bytecode.Ops
import Data.Foldable
import Bytecode.Query
import MMMSpec
import Timing
import Test.QuickCheck

bytecodeSpec :: BytecodeProgSpec ()
bytecodeSpec = BytecodeProgSpec () [
  BytecodeSpec [(["max"], 2)] 4,
  BytecodeSpec [(["+"], 2), (["+"], 2), (["max"], 2)] 4,
  BytecodeSpec [(["-"], 2), (["-"], 2), (["max"], 2)] 4
  ] (BytecodeSpec [(["max"], 2), (["max"], 2)] 3)

bytecodeSketch :: BytecodeProg SymInteger
bytecodeSketch = genSymSimple bytecodeSpec "bc"

gbytecodeSpec :: GroupedBytecodeProgSpec ()
gbytecodeSpec = GroupedBytecodeProgSpec () [
  GroupedBytecodeSpec [[(["max"], 2)]] 4,
  GroupedBytecodeSpec [[(["+"], 2), (["+"], 2)], [(["max"], 2)]] 4,
  GroupedBytecodeSpec [[(["-"], 2), (["-"], 2)], [(["max"], 2)]] 4
  ] (GroupedBytecodeSpec [[(["max"], 2)], [(["max"], 2)]] 3)

gbytecodeSketch :: (Num a, GenSymSimple () a) => BytecodeProg a
gbytecodeSketch = genSymSimple gbytecodeSpec "bc"

bytecodeSpec1 :: BytecodeProgSpec ()
bytecodeSpec1 = BytecodeProgSpec () [
  BytecodeSpec [(["+", "max", "-"], 2), (["+", "max", "-"], 2), (["+", "max", "-"], 2)] 4,
  BytecodeSpec [(["+", "max", "-"], 2), (["+", "max", "-"], 2), (["+", "max", "-"], 2)] 4,
  BytecodeSpec [(["+", "max", "-"], 2), (["+", "max", "-"], 2), (["+", "max", "-"], 2)] 4
  ] (BytecodeSpec [(["max"], 2), (["max"], 2)] 3)

bytecodeSketch1 :: BytecodeProg SymInteger
bytecodeSketch1 = genSymSimple bytecodeSpec1 "bc"

bytecodeMain :: IO ()
bytecodeMain = do
  let configb = precise boolector

  Just mmmIntSynthedBytecode :: Maybe (CBytecodeProg (IntN 6)) <-
    timeItAll "mmmBytecode" $ bytecodeSynth1V configb 1 bytecodeFuncMap () (foldl' (\acc v -> acc &&~ (v >=~ -8) &&~ (v <=~ 8)) (con True) . join)
      (mmmSpecV @(SymIntN 6)) gbytecodeSketch
  print mmmIntSynthedBytecode

  quickCheck
    ( \(l1 :: [Integer]) -> let l :: [IntN 6] = (fromInteger . (\x -> x `mod` 16 - 8) <$> l1) in
        (interpretBytecodeProg [toSym l] (toSym mmmIntSynthedBytecode) bytecodeFuncMap :: ExceptT VerificationConditions UnionM (SymIntN 6))
          == mrgReturn (toSym $ mmmAlgo l :: SymIntN 6)
    )

