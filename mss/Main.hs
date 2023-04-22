module Main where

import Component (componentMain)
import OOPSLA (oopslaMain)
import Common.MainFunc
import ComponentAux
import ComponentListAux
import ComponentList

main :: IO ()
main = mainFunc $ \case
  "oopsla" -> oopslaMain
  "component" -> componentMain
  "componentaux" -> componentAuxMain
  "componentlist" -> componentListMain
  "componentlistaux" -> componentListAuxMain
  _ -> \_ -> do
    oopslaMain ""
    componentMain ""
    componentAuxMain ""
    componentListMain ""
    componentListAuxMain ""
