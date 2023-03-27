module Main where
import Common.MainFunc
import RYOOPSLA
import Component

main :: IO ()
main = mainFunc $ \case
  "ryoopsla" -> ryoopslaMain
  "component" -> componentMain
  _ -> \_ -> do
    ryoopslaMain ""
    componentMain ""

