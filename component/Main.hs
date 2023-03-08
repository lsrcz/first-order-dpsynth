module Main where

import Component.CEGIS
import Component.ConcreteMiniProg
import Component.MiniProg
import Component.Ops
import Data.Maybe
import Grisette

progSpec1 :: MiniProgSpec
progSpec1 =
  MiniProgSpec
    [ ComponentSpec "negate" 1,
      ComponentSpec "+" 2,
      ComponentSpec "+" 2,
      ComponentSpec "max" 2
    ]
    3

prog1 :: MiniProg
prog1 = genSymSimple progSpec1 "prog"

prog2 :: MiniProg
prog2 =
  MiniProg
    [ Node "negate" 0 [mrgReturn $ Input 1],
      Node "+" 1 [mrgReturn $ Input 0, mrgReturn $ Internal 0],
      Node "+" 2 [mrgReturn $ Input 0, mrgReturn $ Internal 1],
      Node "max" 3 [mrgReturn $ Input 2, mrgReturn $ Internal 2]
    ]
    3

cprog2 :: CMiniProg
cprog2 = fromJust $ toCon prog2

{-
ep :: EnhancedMiniProg SymInteger
ep = case runWriterT $ runFreshT (genEnhancedMiniProg [a,b,c] prog2 (chooseSimpleFresh [a, b, c, -b, a-b, a + a - b, symMax (a + a - b) c])) "ep" :: UnionM (EnhancedMiniProg SymInteger, IntermediateVarSet) of
  SingleU (v, _) -> v

keep :: [Int] -> EnhancedMiniProg SymInteger -> EnhancedMiniProg SymInteger
keep v (EnhancedMiniProg n o) = (EnhancedMiniProg [n !! x | x <- v] o)
-}

a :: SymInteger
a = "a"

b :: SymInteger
b = "b"

c :: SymInteger
c = "c"

gen :: M SymInteger
gen = do
  f :: SymInteger =~> SymInteger =~> SymInteger =~> SymInteger <- simpleFresh ()
  mrgReturn (f # "a" # "b" # "c")

{-
gen2 :: M SymInteger
gen2 = do
  chooseSimpleFresh [a, b, c, -b, a-b, a + a - b, symMax (a + a - b) c]
  -}

symMax l r = mrgIte (l >=~ r) l r

{-
v :: M SymInteger
v = interpretMiniProg [a, b, c] prog2 funcMap gen2

v1 :: (UnionM (Either VerificationConditions SymInteger), IntermediateVarSet)
v1 = simpleMerge $ fmap (first mrgReturn) $ runWriterT $ runExceptT $ runFreshT v "ep"

v1r1 :: ExceptT VerificationConditions UnionM ()
v1r1 = do
  x <- ExceptT $ fst v1
  symAssert $ x ==~ symMax (a+a-b) c

v1i :: IntermediateVarSet
v1i = snd v1
-}

main :: IO ()
main = do
  Right (_, r) <-
    cegisCustomized
      (precise z3)
      (\x -> x ==~ symMax (a + a - b) c)
      [a, b, c]
      prog1
      funcMap
      gen
  print r
  print $ evaluateSym False r prog1

{-
  print $ (interpretCMiniProg [a,b,c] cprog2 funcMap :: ExceptT VerificationConditions UnionM SymInteger)

  throw DivideByZero
  --print prog1
  print ep
  let ee1 = evaluateSym False (buildModel (("a" :: TypedSymbol Integer) ::= (-3), ("b" :: TypedSymbol Integer) ::= (-2), ("c" :: TypedSymbol Integer) ::= (-2))) ep
  let ee2 = evaluateSym False (buildModel (("a" :: TypedSymbol Integer) ::= 0, ("b" :: TypedSymbol Integer) ::= 0, ("c" :: TypedSymbol Integer) ::= 1)) ep
  let ee3 = evaluateSym False (buildModel (("a" :: TypedSymbol Integer) ::= 1, ("b" :: TypedSymbol Integer) ::= 0, ("c" :: TypedSymbol Integer) ::= 0)) ep

  let exx :: ExceptT VerificationConditions UnionM () = do
       connected $ keep [0,1,2,6] ee2
       connected $ keep [0,1,2,6] ee3
  putStrLn "ee2"
  print (keep [0,1,2,6] $ ee2)
  putStrLn "ee3"
  print (keep [0,1,2,6] $ ee3)
  putStrLn "cee2"
  print (connected $ keep [0,1,2,6] ee2 :: ExceptT VerificationConditions UnionM ())
  putStrLn "cee3"
  print (connected $ keep [0,1,2,6] ee3 :: ExceptT VerificationConditions UnionM ())
  m <- solveExcept (precise $ z3) (\case Left _ -> con False; _ -> con True)exx
  case m of
    Left sf -> print sf
    Right mo -> print mo

  Right x <- return m

  -- print ep
  --print v1
  --print v1r1
  -- Right r1 <- solveExcept (precise z3) (\case Left _ -> con False; _ -> con True) v1r1
  --print r1
  -- print $ evaluateSym False r1 prog1
  (_, Right r) <- cegisExceptStdVC (precise z3) (a, b, c) v1r1
  print r
  -- print $ evaluateSym False r ep
  print $ evaluateSym False r prog2

-}
