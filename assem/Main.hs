module Main where

import Control.Monad.Except
import Core
import Data.Foldable
import Data.List
import Data.Proxy
import Gen
import Grisette
import Ops
import Query
import Timing

assem :: Num a => ConProgram a
assem =
  ConProgram
    -- stay1 switch1 stay2 switch2
    [0, 0]
    [ ConBinary
        "min"
        (ConBinary "+" (ConArg 4) (ConArg 0))
        (ConBinary "+" (ConArg 5) (ConArg 1)),
      ConBinary
        "min"
        (ConBinary "+" (ConArg 5) (ConArg 2))
        (ConBinary "+" (ConArg 4) (ConArg 3))
    ]
    (ConBinary "min" (ConArg 0) (ConArg 1))
    -- stay switch
    4

assemSketchComb :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s, Show s) => proxy c -> Program s
assemSketchComb _ =
  genSymSimple
    (CombProgramSpec @c @s [0] (CombASTSpec0 1 3 ["zero", "id"] ["+", "min"]) (CombASTSpec0 0 1 [] ["min"]) 2 4)
    "assem"

assemSketchExt :: forall proxy c s. (ToSym c s, Num c, Num s, SimpleMergeable s, Show s) => proxy c -> Program s
assemSketchExt _ =
  genSymSimple
    (ExtProgramSpec @c @s [0] (CombASTSpec0 1 1 ["zero", "id"] ["+"]) "min" 2 2 2 4)
    "assemopt"

assemAlgo :: forall a. (Show a, Num a, Ord a) => [[a]] -> a
assemAlgo = go 0 0
  where
    go line1 line2 [] = min line1 line2
    go line1 line2 ([stay1, switch1, stay2, switch2] : xs) =
      {-trace (show line1) $ trace (show line2) $ trace (show x) $-}
      go (min (line1 + stay1) (line2 + switch1)) (min (line2 + stay2) (line1 + switch2)) xs
    go _ _ _ = undefined

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
allSpec 1 1 = [[Stay1], [Switch2]]
allSpec 1 2 = [[Stay2], [Switch1]]
allSpec n 1 = [Stay1 : x | x <- allSpec (n - 1) 1] ++ [Switch2 : x | x <- allSpec (n - 1) 2]
allSpec n 2 = [Stay2 : x | x <- allSpec (n - 1) 2] ++ [Switch1 : x | x <- allSpec (n - 1) 1]
allSpec _ _ = undefined

apply :: (Num a) => [[a]] -> [S] -> a
apply [] [] = 0
apply ([stay1, _, _, _] : xs) (Stay1 : ys) = stay1 + apply xs ys
apply ([_, switch1, _, _] : xs) (Switch1 : ys) = switch1 + apply xs ys
apply ([_, _, stay2, _] : xs) (Stay2 : ys) = stay2 + apply xs ys
apply ([_, _, _, switch2] : xs) (Switch2 : ys) = switch2 + apply xs ys
apply _ _ = undefined

assemSpec :: forall a e. (Show a, Num a, SOrd a, SimpleMergeable a, SafeLinearArith e a) => [[a]] -> ExceptT VerificationConditions UnionM a
assemSpec inputs =
  mrgReturn $ trav (sort $ allSpec (length inputs) 1 ++ allSpec (length inputs) 2)
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
    t = map (apply inputs) $ allSpec (length inputs) 1 ++ allSpec (length inputs) 2

cap :: (SOrd a, Num a) => [[a]] -> SymBool
cap = foldl (\acc y -> acc &&~ y >=~ -16 &&~ y <=~ 16) (con True) . join

main :: IO ()
main = do
  let config = precise z3

  assemIntSynthedExtV :: Maybe (ConProgram Integer) <-
    timeItAll "assembextV" $ synth1V config availableUnary availableBinary () (const $ con True) (assemSpecV @SymInteger) (assemSketchExt (Proxy @Integer))
  print assemIntSynthedExtV

  assemIntSynthedCombV :: Maybe (ConProgram Integer) <-
    timeItAll "assembcombV" $ synth1V config availableUnary availableBinary () (const $ con True) (assemSpecV @SymInteger) (assemSketchComb (Proxy @Integer))
  print assemIntSynthedCombV
