module Main where

import OOPSLA (oopslaMain)
import Component (componentMain)

main :: IO ()
main = do
  componentMain
  oopslaMain
