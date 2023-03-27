module Component.QuickCheck where

import Common.Val
import Component.ConcreteProg
import Component.Ops
import Control.Monad.Except
import Data.Proxy
import Debug.Trace
import Grisette
import Test.QuickCheck
import Common.T

qcComponent ::
  forall v i s.
  ( CValLike v,
    Show s,
    Num s,
    SOrd s,
    Eq s,
    LinkedRep i s,
    ToSym i s,
    SimpleMergeable s
  ) =>
  Proxy s ->
  Integer ->
  Integer ->
  Integer ->
  ([Integer] -> Integer) ->
  CProg v i ->
  IO ()
qcComponent _ m off n algo p =
  quickCheck
    ( \(l1 :: [Integer]) ->
        let l = (\x -> x `mod` m - off) <$> take (fromInteger n) l1
            leftResult = (interpretCProg [fromInteger <$> l] p funcMap :: ExceptT VerificationConditions UnionM s)
            rightResult = mrgReturn (fromInteger $ algo l :: s)
         in ((leftResult == rightResult) || trace (show l) (trace (show leftResult) (trace (show rightResult) False)))
    )

px4 :: [(Integer, Integer, Integer, Integer)] -> [[Integer]]
px4 [] = [[], [], [], []]
px4 ((a, b, c, d) : xs) = case px4 xs of
  [as, bs, cs, ds] -> [a : as, b : bs, c : cs, d : ds]
  _ -> undefined

qcComponent4 ::
  forall v i s.
  ( CValLike v,
    Show s,
    Num s,
    SOrd s,
    Eq s,
    LinkedRep i s,
    ToSym i s,
    SimpleMergeable s
  ) =>
  Proxy s ->
  Integer ->
  Integer ->
  Integer ->
  ([[Integer]] -> Integer) ->
  CProg v i ->
  IO ()
qcComponent4 _ m off n algo p =
  quickCheck
    ( \(l1 :: [(Integer, Integer, Integer, Integer)]) ->
        let l = (fmap . fmap) (\x -> x `mod` m - off) $ px4 $ take (fromInteger n) l1
            leftResult = (interpretCProg ((fmap . fmap) fromInteger l) p funcMap :: ExceptT VerificationConditions UnionM s)
            rightResult = mrgReturn (fromInteger $ algo l :: s)
         in ((leftResult == rightResult) || trace (show l) (trace (show leftResult) (trace (show rightResult) False)))
    )

qcTComponent ::
  forall v i s.
  ( CValLike v,
    Show s,
    Num s,
    SOrd s,
    Eq s,
    LinkedRep i s,
    ToSym i s,
    SimpleMergeable s
  ) =>
  Proxy s ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  ([Integer] -> Integer) ->
  CProg v (CT i) ->
  IO ()
qcTComponent _ m off minListSize maxListSize algo p =
  quickCheck
    ( \(l1 :: [Integer]) ->
        let l = (\x -> x `mod` m - off) <$> take (fromInteger maxListSize) l1
            leftResult = (interpretCProg [mrgReturn . TInt . fromInteger <$> l] p mtfuncMap :: ExceptT VerificationConditions UnionM (MT s))
            rightResult = mrgReturn (mrgReturn . TInt . fromInteger $ algo l :: MT s)
         in toInteger (length l1) < minListSize || ((leftResult == rightResult) || trace (show l) (trace (show leftResult) (trace (show rightResult) False)))
    )
