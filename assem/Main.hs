module Main where

import Component (componentMain)
import OOPSLA
import Common.MainFunc

main :: IO ()
main = mainFunc $ \case
  "component" -> componentMain
  "oopsla" -> oopslaMain
  _ -> \_ -> do
    componentMain ""
    oopslaMain ""
