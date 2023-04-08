module Main where

import Component (componentMain)
import OOPSLA
import Common.MainFunc
import ComponentAux

main :: IO ()
main = mainFunc $ \case
  "component" -> componentMain
  "componentaux" -> componentAuxMain
  "oopsla" -> oopslaMain
  _ -> \_ -> do
    componentMain ""
    componentAuxMain ""
    oopslaMain ""
