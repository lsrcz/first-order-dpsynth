module LongestEvenZeroSpec where

import Grisette
import Control.Monad

longestEvenZero :: (Num a, Integral a) => [a] -> a
longestEvenZero = go 0 0
  where
    go maxLength _ [] = maxLength
    go maxLength current (0:xs) =
      let
        newCurrent = current + 1
       in
        if even newCurrent
          then go (max maxLength newCurrent) newCurrent xs
          else go maxLength newCurrent xs
    go maxLength _ (_:xs) = go maxLength 0 xs
    
restrictedLongestEvenSpecCon ::
  forall c.
  (Show c, Num c, Integral c) =>
  [[c]] ->
  Either VerificationConditions c
restrictedLongestEvenSpecCon l = do
  return $ longestEvenZero $ join l

