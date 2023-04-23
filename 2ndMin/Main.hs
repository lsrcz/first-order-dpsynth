module Main where
import Common.MainFunc
import RYOOPSLA
import Component
import ComponentList

main :: IO ()
main = mainFunc $ \case
  "ryoopsla" -> ryoopslaMain
  "component" -> componentMain
  "componentlist" -> componentListMain
  _ -> \_ -> do
    ryoopslaMain ""
    componentMain ""
    componentListMain ""
