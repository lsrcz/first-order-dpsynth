module Main where

import Bytecode
import Component
import OOPSLA
import Common.MainFunc

-- Component

main :: IO ()
main = mainFunc $ \case
  "oopsla" -> oopslaMain
  "component" -> componentMain
  "bytecode" -> bytecodeMain
  _ -> \_ -> do
    oopslaMain ""
    componentMain ""
    bytecodeMain ""
