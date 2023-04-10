module Component.QuickCheck where

import Common.FuncMap
import Common.Val
import Component.ConcreteProg
import Component.Ops
import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as M
import Data.Proxy
import Debug.Trace
import Grisette
import Test.QuickCheck
import Common.T

qcComponent ::
  forall v c.
  ( CValLike v,
    Num c,
    Ord c,
    Show c
  ) =>
  Integer ->
  Integer ->
  Integer ->
  ([Integer] -> Integer) ->
  CProg B.ByteString v c ->
  IO ()
qcComponent m off n algo p =
  quickCheck
    ( \(l1 :: [Integer]) ->
        let l = (\x -> x `mod` m - off) <$> take (fromInteger n) l1
            leftResult =
              ( interpretCProgOnConInputs [fromInteger <$> l] p cfuncMap :: Either VerificationConditions c
              )
            rightResult = Right $ fromInteger $ algo l
         in ((leftResult == rightResult) || trace (show l) (trace (show leftResult) (trace (show rightResult) False)))
    )

px4 :: [(Integer, Integer, Integer, Integer)] -> [[Integer]]
px4 [] = [[], [], [], []]
px4 ((a, b, c, d) : xs) = case px4 xs of
  [as, bs, cs, ds] -> [a : as, b : bs, c : cs, d : ds]
  _ -> undefined

qcComponent4 ::
  forall v c.
  ( CValLike v,
    Num c,
    Ord c,
    Show c
  ) =>
  Integer ->
  Integer ->
  Integer ->
  ([[Integer]] -> Integer) ->
  CProg B.ByteString v c ->
  IO ()
qcComponent4 m off n algo p =
  quickCheck
    ( \(l1 :: [(Integer, Integer, Integer, Integer)]) ->
        let l = (fmap . fmap) (\x -> x `mod` m - off) $ px4 $ take (fromInteger n) l1
            leftResult = (interpretCProgOnConInputs ((fmap . fmap) fromInteger l) p cfuncMap :: Either VerificationConditions c)
            rightResult = Right $ fromInteger $ algo l
         in ((leftResult == rightResult) || trace (show l) (trace (show leftResult) (trace (show rightResult) False)))
    )

qcTComponent ::
  forall v c.
  ( CValLike v,
    Ord c,
    Show c,
    Num c
  ) =>
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  ([Integer] -> Integer) ->
  CProg B.ByteString v (CT c) ->
  IO ()
qcTComponent m off minListSize maxListSize algo p =
  quickCheck
    ( \(l1 :: [Integer]) ->
        let l = (\x -> x `mod` m - off) <$> take (fromInteger maxListSize) l1
            leftResult = (interpretCProgOnConInputs [CInt . fromInteger <$> l] p mtcfuncMap :: Either VerificationConditions (CT c))
            rightResult = Right (CInt . fromInteger $ algo l :: CT c)
         in toInteger (length l1) < minListSize || ((leftResult == rightResult) || trace (show l) (trace (show leftResult) (trace (show rightResult) False)))
    )
