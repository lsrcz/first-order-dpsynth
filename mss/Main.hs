module Main where

import Component (componentMain)
import OOPSLA (oopslaMain)
import Common.MainFunc
import ComponentAux

main :: IO ()
main = mainFunc $ \case
  "oopsla" -> oopslaMain
  "component" -> componentMain
  "componentaux" -> componentAuxMain
  _ -> \_ -> do
    oopslaMain ""
    componentMain ""
    componentAuxMain ""
