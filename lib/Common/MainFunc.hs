{-# LANGUAGE DeriveDataTypeable #-}
module Common.MainFunc where

import System.Environment
import Data.Data
import System.Console.CmdArgs

data Args = Args {algorithm :: String, arg :: String}
  deriving (Show, Data, Typeable)

defaultArgs :: Args
defaultArgs = Args "" ""

mainFunc :: (String -> String -> IO ()) -> IO ()
mainFunc f = do
  a <- cmdArgs defaultArgs
  f (algorithm a) (arg a)
