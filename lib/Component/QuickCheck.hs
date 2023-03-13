module Component.QuickCheck where

import Component.ConcreteProg
import Component.Ops
import Control.Monad.Except
import Grisette
import Test.QuickCheck
import Common.Val
import Data.Proxy
import Debug.Trace

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
