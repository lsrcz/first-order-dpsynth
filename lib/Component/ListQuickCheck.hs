module Component.ListQuickCheck where
import Common.Val
import Component.ListProg
import Grisette
import Test.QuickCheck
import Debug.Trace
import Component.ListOps (listAuxcfuncMap, listCombcfuncMap)


qcListProg1 ::
  forall v c.
  ( CValLike v,
    Integral c,
    Num c,
    Ord c,
    Show c
  ) =>
  Integer ->
  Integer ->
  Integer ->
  ([Integer] -> Integer) ->
  CListProg v c ->
  IO ()
qcListProg1 m off n algo p =
  quickCheck ( \(l1 :: [Integer]) ->
        let l = (\x -> x `mod` m - off) <$> take (fromInteger n) l1
            leftResult =
              ( interpretCListProgOnConInputs [fromInteger <$> l] (fromInteger $ algo l) p listAuxcfuncMap listCombcfuncMap :: Either VerificationConditions c
              )
            rightResult = Right $ fromInteger $ algo l
         in (length l <= 1 || (leftResult == rightResult) || trace (show l) (trace (show leftResult) (trace (show rightResult) False))))

    
