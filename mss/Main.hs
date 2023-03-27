module Main where

import Component (componentMain)
import OOPSLA (oopslaMain)
import Common.MainFunc

main :: IO ()
main = mainFunc $ \case
  "oopsla" -> oopslaMain
  "component" -> componentMain
  _ -> \_ -> do
    oopslaMain ""
    componentMain ""
