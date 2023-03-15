module ASSEMSpec where

import Control.Monad.Except
import Data.Foldable
import Data.List
import Debug.Trace
import Grisette

assemAlgoTransposed :: forall a. (Show a, Num a, Ord a) => [[a]] -> a
assemAlgoTransposed = go 0 0
  where
    go line1 line2 [] = min line1 line2
    go line1 line2 ([stay1, switch1, stay2, switch2] : xs) =
      {-trace (show line1) $ trace (show line2) $ trace (show x) $-}
      go (min (line1 + stay1) (line2 + switch1)) (min (line2 + stay2) (line1 + switch2)) xs
    go _ _ _ = undefined

assemAlgo :: forall a. (Show a, Num a, Ord a) => [[a]] -> a
assemAlgo = assemAlgoTransposed . transpose

data S = Stay1 | Switch1 | Stay2 | Switch2 deriving (Show, Eq, Ord)

startPosition :: S -> Int
startPosition Stay1 = 1
startPosition Switch1 = 2
startPosition Stay2 = 2
startPosition Switch2 = 1

endPosition :: S -> Int
endPosition Stay1 = 1
endPosition Switch1 = 1
endPosition Stay2 = 2
endPosition Switch2 = 2

allSpec :: Int -> Int -> [[S]]
allSpec 0 _ = [[], []]
allSpec 1 1 = [[Stay1], [Switch2]]
allSpec 1 2 = [[Stay2], [Switch1]]
allSpec n 1 = [Stay1 : x | x <- allSpec (n - 1) 1] ++ [Switch2 : x | x <- allSpec (n - 1) 2]
allSpec n 2 = [Stay2 : x | x <- allSpec (n - 1) 2] ++ [Switch1 : x | x <- allSpec (n - 1) 1]
allSpec _ _ = undefined

applyTransposed :: (Show a, Num a) => [[a]] -> [S] -> a
applyTransposed [] [] = 0
applyTransposed ([stay1, _, _, _] : xs) (Stay1 : ys) = stay1 + applyTransposed xs ys
applyTransposed ([_, switch1, _, _] : xs) (Switch1 : ys) = switch1 + applyTransposed xs ys
applyTransposed ([_, _, stay2, _] : xs) (Stay2 : ys) = stay2 + applyTransposed xs ys
applyTransposed ([_, _, _, switch2] : xs) (Switch2 : ys) = switch2 + applyTransposed xs ys
applyTransposed l r = undefined

apply :: (Show a, Num a) => [[a]] -> [S] -> a
apply x = applyTransposed $ transpose x

assemSpec :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
assemSpec inputs =
  mrgReturn $ trav (sort $ allSpec (length $ head inputs) 1 ++ allSpec (length $ head inputs) 2)
  where
    trav [] = undefined
    trav [v] = apply inputs v
    trav (v : vs) = let a = apply inputs v; acc = trav vs in mrgIte (a <=~ acc) a acc

assemSpecV :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> a -> ExceptT VerificationConditions UnionM SymBool
assemSpecV inputs v =
  mrgReturn $
    foldl' (\acc x -> acc &&~ v <=~ x) (con True) t
      &&~ foldl' (\acc x -> acc ||~ v ==~ x) (con False) t
  where
    t = map (apply inputs) $ allSpec (length $ head inputs) 1 ++ allSpec (length $ head inputs) 2
