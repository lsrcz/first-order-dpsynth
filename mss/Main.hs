module Main where

import Component (componentMain)
import OOPSLA (oopslaMain)

main :: IO ()
main = do
  componentMain
  oopslaMain
