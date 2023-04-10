{-# LANGUAGE UndecidableInstances #-}
module Component.ListOps where

import Common.FuncMap
import Common.ListProg
import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as M
import Data.List (foldl1')
import GHC.Generics
import Grisette
import Data.Maybe
import Component.Ops

mlList2IntUnaryFunc ::
  Mergeable si =>
  ( forall m.
    ( MonadError VerificationConditions m,
      MonadUnion m,
      MonadFresh m
    ) =>
    [si] ->
    m si
  ) ->
  Func (MListProgVal si)
mlList2IntUnaryFunc f = Func 1 False $ \case
  [a] -> do
    r <- liftToMonadUnion a
    case r of
      LIntList l -> mrgFmap (mrgReturn . LInt) $ f l
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

mlInt2IntUnaryFunc :: Mergeable si => (forall m. (MonadError VerificationConditions m, MonadUnion m) => si -> m si) -> Func (MListProgVal si)
mlInt2IntUnaryFunc f = Func 1 False $ \case
  [a] -> do
    r <- liftToMonadUnion a
    case r of
      LInt v -> mrgFmap (mrgReturn . LInt) $ f v
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

mlList2ListUnaryFunc :: Mergeable si => (forall m. (MonadError VerificationConditions m, MonadUnion m, MonadFresh m) => [si] -> m [si]) -> Func (MListProgVal si)
mlList2ListUnaryFunc f = Func 1 False $ \case
  [a] -> do
    r <- liftToMonadUnion a
    case r of
      LIntList v -> mrgFmap (mrgReturn . LIntList) $ f v
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

mlIntInt2IntUnaryFunc ::
  Mergeable si =>
  Bool ->
  ( forall m.
    ( MonadError VerificationConditions m,
      MonadUnion m,
      MonadFresh m
    ) =>
    si ->
    si ->
    m si
  ) ->
  Func (MListProgVal si)
mlIntInt2IntUnaryFunc comm f = Func 2 comm $ \case
  [v1, v2] -> do
    v1' <- liftToMonadUnion v1
    v2' <- liftToMonadUnion v2
    case (v1', v2') of
      (LInt i1, LInt i2) -> mrgFmap (mrgReturn . LInt) $ f i1 i2
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

mlIntList2IntBinaryFunc ::
  Mergeable si =>
  ( forall m.
    ( MonadError VerificationConditions m,
      MonadUnion m,
      MonadFresh m
    ) =>
    si ->
    [si] ->
    m si
  ) ->
  Func (MListProgVal si)
mlIntList2IntBinaryFunc f = Func 2 False $ \case
  [v1, v2] -> do
    v1' <- liftToMonadUnion v1
    v2' <- liftToMonadUnion v2
    case (v1', v2') of
      (LInt i1, LIntList i2) -> mrgFmap (mrgReturn . LInt) $ f i1 i2
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

mlIntList2ListBinaryFunc ::
  Mergeable si =>
  ( forall m.
    ( MonadError VerificationConditions m,
      MonadUnion m,
      MonadFresh m
    ) =>
    si ->
    [si] ->
    m [si]
  ) ->
  Func (MListProgVal si)
mlIntList2ListBinaryFunc f = Func 2 False $ \case
  [v1, v2] -> do
    v1' <- liftToMonadUnion v1
    v2' <- liftToMonadUnion v2
    case (v1', v2') of
      (LInt i1, LIntList i2) -> mrgFmap (mrgReturn . LIntList) $ f i1 i2
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

mlListList2ListBinaryFunc ::
  Mergeable si =>
  ( forall m.
    ( MonadError VerificationConditions m,
      MonadUnion m,
      MonadFresh m
    ) =>
    [si] ->
    [si] ->
    m [si]
  ) ->
  Func (MListProgVal si)
mlListList2ListBinaryFunc f = Func 2 False $ \case
  [v1, v2] -> do
    v1' <- liftToMonadUnion v1
    v2' <- liftToMonadUnion v2
    case (v1', v2') of
      (LIntList i1, LIntList i2) -> mrgFmap (mrgReturn . LIntList) $ f i1 i2
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation




---- CFunc ----
mlList2IntUnaryCFunc ::
  ( [ci] ->
    Either VerificationConditions ci
  ) ->
  CFunc (CListProgVal ci)
mlList2IntUnaryCFunc f = CFunc 1 False $ \case
  [a] -> do
    case a of
      CLIntList l -> CLInt <$> f l
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

mlInt2IntUnaryCFunc :: (ci -> Either VerificationConditions ci) -> CFunc (CListProgVal ci)
mlInt2IntUnaryCFunc f = CFunc 1 False $ \case
  [a] -> do
    case a of
      CLInt v -> CLInt <$> f v
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

mlList2ListUnaryCFunc :: ([ci] -> Either VerificationConditions [ci]) -> CFunc (CListProgVal ci)
mlList2ListUnaryCFunc f = CFunc 1 False $ \case
  [a] -> do
    case a of
      CLIntList v -> CLIntList <$> f v
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

mlIntInt2IntUnaryCFunc ::
  Bool ->
  ( ci ->
    ci ->
    Either VerificationConditions ci
  ) ->
  CFunc (CListProgVal ci)
mlIntInt2IntUnaryCFunc comm f = CFunc 2 comm $ \case
  [v1, v2] -> do
    case (v1, v2) of
      (CLInt i1, CLInt i2) -> CLInt <$> f i1 i2
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

mlIntList2IntBinaryCFunc ::
  ( ci ->
    [ci] ->
    Either VerificationConditions ci
  ) ->
  CFunc (CListProgVal ci)
mlIntList2IntBinaryCFunc f = CFunc 2 False $ \case
  [v1, v2] -> do
    case (v1, v2) of
      (CLInt i1, CLIntList i2) -> CLInt <$> f i1 i2
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

mlIntList2ListBinaryCFunc ::
  ( ci ->
    [ci] ->
    Either VerificationConditions [ci]
  ) ->
  CFunc (CListProgVal ci)
mlIntList2ListBinaryCFunc f = CFunc 2 False $ \case
  [v1, v2] -> do
    case (v1, v2) of
      (CLInt i1, CLIntList i2) -> CLIntList <$> f i1 i2
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

mlListList2ListBinaryCFunc ::
  ( [ci] ->
    [ci] ->
    Either VerificationConditions [ci]
  ) ->
  CFunc (CListProgVal ci)
mlListList2ListBinaryCFunc f = CFunc 2 False $ \case
  [v1, v2] -> do
    case (v1, v2) of
      (CLIntList i1, CLIntList i2) -> CLIntList <$> f i1 i2
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

data MLOpCode si
  = MLSOp B.ByteString
  | MLSOpConst B.ByteString si
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (MLOpCode si))

data CMLOpCode ci
  = CMLSOp B.ByteString
  | CMLSOpConst B.ByteString ci
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default (CMLOpCode ci))

deriving via (Default (MLOpCode si)) instance ToCon si si => ToCon (MLOpCode si) (MLOpCode si)

deriving via (Default (CMLOpCode ci)) instance ToCon si ci => ToCon (MLOpCode si) (CMLOpCode ci)

instance (Show si, EvaluateSym si, ToCon si si) => OpCode (MLOpCode si) (B.ByteString, Bool) where
  opGroup (MLSOp o) = (o, False)
  opGroup (MLSOpConst o _) = (o, True)

intToBoolFunction :: (MonadError VerificationConditions m, MonadUnion m, MonadFresh m, GenSymSimple () si, SOrd si, Num si) => si -> si -> m SymBool
intToBoolFunction opc v =
  mrgIf (opc ==~ 0) (mrgReturn $ v >~ 0) $
    mrgIf (opc ==~ 1) (mrgReturn $ v <~ 0) $
      mrgIf
        (opc ==~ 2)
        ( do
            t <- simpleFresh ()
            symAssert (t + t ==~ v ||~ t + t + 1 ==~ v)
            mrgReturn $ t + t ==~ v
        )
        ( do
            t <- simpleFresh ()
            symAssert (t + t ==~ v ||~ t + t + 1 ==~ v)
            mrgReturn $ t + t + 1 ==~ v
        )

intIntToIntCommLinearFunction ::
  ( MonadError VerificationConditions m,
    MonadUnion m,
    MonadFresh m,
    SOrd si,
    Num si,
    SimpleMergeable si
  ) =>
  si ->
  si ->
  si ->
  m si
intIntToIntCommLinearFunction opc v1 v2 =
  mrgIf (opc ==~ 0) (mrgReturn $ v1 + v2) $
    mrgIf (opc ==~ 1) (mrgReturn $ symMin v1 v2) (mrgReturn $ symMax v1 v2)

intToBoolCFunction :: (Ord ci, Num ci, Integral ci) => ci -> ci -> Either VerificationConditions Bool
intToBoolCFunction opc v =
  case opc of
    0 -> return $ v > 0
    1 -> return $ v < 0
    2 -> return $ even v
    _ -> return $ odd v

intIntToIntCommLinearCFunction ::
  (Ord ci, Num ci) => ci -> ci -> ci ->
  Either VerificationConditions ci
intIntToIntCommLinearCFunction opc v1 v2 =
  case opc of
    0 -> return $ v1 + v2
    1 -> return $ min v1 v2
    _ -> return $ max v1 v2

access ::
  ( MonadError VerificationConditions m,
    MonadUnion m,
    SimpleMergeable si,
    SEq si,
    Num si
  ) =>
  si ->
  [si] ->
  m si
access _ [] = mrgThrowError AssertionViolation
access i (x : xs) = mrgIf (i ==~ 0) (return x) (access (i - 1) xs)

takeFunc ::
  ( MonadError VerificationConditions m,
    MonadUnion m,
    SimpleMergeable si,
    SOrd si,
    Num si
  ) =>
  si ->
  [si] ->
  m [si]
takeFunc i1 l1 = do
  symAssert $ i1 >=~ 0
  go i1 l1
  where
    go i l =
      mrgIf
        (i ==~ 0)
        (return [])
        ( case l of
            [] -> mrgThrowError AssertionViolation
            (x : xs) -> do
              r <- go (i - 1) xs
              mrgReturn $ x : r
        )

dropFunc ::
  ( MonadError VerificationConditions m,
    MonadUnion m,
    SimpleMergeable si,
    SOrd si,
    Num si
  ) =>
  si ->
  [si] ->
  m [si]
dropFunc i1 l1 = do
  symAssert $ i1 >=~ 0
  go i1 l1
  where
    go i l =
      mrgIf
        (i ==~ 0)
        (return l)
        ( case l of
            [] -> mrgThrowError AssertionViolation
            (_ : xs) -> go (i - 1) xs
        )

filterFunc ::
  ( MonadError VerificationConditions m,
    MonadUnion m,
    MonadFresh m,
    GenSymSimple () si,
    SimpleMergeable si,
    SOrd si,
    Num si
  ) =>
  si ->
  [si] ->
  m [si]
filterFunc _ [] = mrgReturn []
filterFunc opc (x:xs) = do
  curr <- intToBoolFunction opc x
  remaining <- filterFunc opc xs
  mrgIf curr (mrgReturn $ x:remaining) (mrgReturn remaining)

zipFunc ::
  ( MonadError VerificationConditions m,
    MonadUnion m,
    MonadFresh m,
    GenSymSimple () si,
    SimpleMergeable si,
    SOrd si,
    Num si
  ) =>
  (si -> si -> m si) ->
  [si] ->
  [si] ->
  m [si]
zipFunc _ [] _ = mrgReturn []
zipFunc _ _ [] = mrgReturn []
zipFunc f (x:xs) (y:ys)= do
  curr <- f x y
  remaining <- zipFunc f xs ys
  mrgReturn $ curr : remaining

zipCommLinearFunc ::
  ( MonadError VerificationConditions m,
    MonadUnion m,
    MonadFresh m,
    GenSymSimple () si,
    SimpleMergeable si,
    SOrd si,
    Num si
  ) =>
  si ->
  [si] ->
  [si] ->
  m [si]
zipCommLinearFunc opc = zipFunc (intIntToIntCommLinearFunction opc)

scanlFunc ::
  ( MonadError VerificationConditions m,
    MonadUnion m,
    MonadFresh m,
    GenSymSimple () si,
    SimpleMergeable si,
    SOrd si,
    Num si
  ) =>
  (si -> si -> m si) ->
  [si] ->
  m [si]
scanlFunc _ [] = mrgReturn []
scanlFunc f (x:xs) = go x xs
  where
    go acc [] = mrgReturn [acc]
    go acc (y:ys) = do
      nextAcc <- f acc y
      rest <- go nextAcc ys
      mrgReturn (acc:rest)

scanrFunc ::
  ( MonadError VerificationConditions m,
    MonadUnion m,
    MonadFresh m,
    GenSymSimple () si,
    SimpleMergeable si,
    SOrd si,
    Num si
  ) =>
  (si -> si -> m si) ->
  [si] ->
  m [si]
scanrFunc f l = do
  r <- scanlFunc (flip f) (reverse l)
  mrgReturn $ reverse r

scanlCFunc ::
  ( Ord ci,
    Num ci
  ) =>
  (ci -> ci -> Either VerificationConditions ci) ->
  [ci] ->
  Either VerificationConditions [ci]
scanlCFunc _ [] = return []
scanlCFunc f (x:xs) = go x xs
  where
    go acc [] = return [acc]
    go acc (y:ys) = do
      nextAcc <- f acc y
      rest <- go nextAcc ys
      return (acc:rest)

scanrCFunc ::
  ( Ord ci,
    Num ci
  ) =>
  (ci -> ci -> Either VerificationConditions ci) ->
  [ci] ->
  Either VerificationConditions [ci]
scanrCFunc f l = do
  r <- scanlCFunc (flip f) (reverse l)
  return $ reverse r

newtype MLFuncMap a = 
  MLFuncMap (M.HashMap B.ByteString (Either (Func (MListProgVal a)) (a -> Func (MListProgVal a))))

mlfuncMap :: (Num a, SOrd a, SimpleMergeable a, GenSymSimple () a) => MLFuncMap a
mlfuncMap = MLFuncMap $
  M.fromList
    [ ( "intConst",
        Right $ \x -> Func 0 False $ \case
          [] -> mrgReturn $ mrgReturn $ LInt x
          _ -> mrgThrowError AssertionViolation
      ),
      ( "binCommLinear",
        Right $ \opc ->
          mlIntInt2IntUnaryFunc True $ \l r -> intIntToIntCommLinearFunction opc l r
      ),
      ("binMinus", Left $ mlIntInt2IntUnaryFunc False $ \l r -> mrgReturn $ l - r),
      ("binTimes", Left $ mlIntInt2IntUnaryFunc True $ \l r -> mrgReturn $ l * r),
      ("sum", Left $ mlList2IntUnaryFunc $ mrgReturn . sum),
      ("len", Left $ mlList2IntUnaryFunc $ mrgReturn . fromIntegral . length),
      ("head", Left $ mlList2IntUnaryFunc $ mrgReturn . head),
      ("last", Left $ mlList2IntUnaryFunc $ mrgReturn . last),
      ("access", Left $ mlIntList2IntBinaryFunc access),
      ( "count",
        Right $ \opc -> mlList2IntUnaryFunc $ do
          foldM
            ( \acc va -> do
                r <- intToBoolFunction opc va
                mrgReturn $ mrgIte r (acc + 1) acc
            )
            0
      ),
      ("min", Left $ mlList2IntUnaryFunc $ mrgReturn . foldl1' symMin),
      ("max", Left $ mlList2IntUnaryFunc $ mrgReturn . foldl1' symMax),
      ("neg", Left $ mlInt2IntUnaryFunc $ mrgReturn . negate),
      ("take", Left $ mlIntList2ListBinaryFunc takeFunc),
      ("drop", Left $ mlIntList2ListBinaryFunc dropFunc),
      ("reverse", Left $ mlList2ListUnaryFunc $ mrgReturn . reverse),
      ("offset", Right $ \x -> mlList2ListUnaryFunc $ \l -> mrgReturn $ map (+x) l),
      ("negateList", Left $ mlList2ListUnaryFunc $ \l -> mrgReturn $ map negate l),
      ("filter", Right $ \opc -> mlList2ListUnaryFunc $ \l -> filterFunc opc l),
      ("zipCommLinear", Right $ \opc -> mlListList2ListBinaryFunc $ zipFunc (intIntToIntCommLinearFunction opc)),
      ("zipMinus", Left $ mlListList2ListBinaryFunc $ zipFunc $ \l r -> mrgReturn $ l - r),
      ("zipTimes", Left $ mlListList2ListBinaryFunc $ zipFunc $ \l r -> mrgReturn $ l * r),
      ("scanlCommLinear", Right $ \opc -> mlList2ListUnaryFunc $ scanlFunc (intIntToIntCommLinearFunction opc)),
      ("scanlMinus", Left $ mlList2ListUnaryFunc $ scanlFunc (\l r -> mrgReturn $ l - r)),
      ("scanlTimes", Left $ mlList2ListUnaryFunc $ scanlFunc (\l r -> mrgReturn $ l * r)),
      ("scanrCommLinear", Right $ \opc -> mlList2ListUnaryFunc $ scanrFunc (intIntToIntCommLinearFunction opc)),
      ("scanrMinus", Left $ mlList2ListUnaryFunc $ scanrFunc (\l r -> mrgReturn $ l - r)),
      ("scanrTimes", Left $ mlList2ListUnaryFunc $ scanrFunc (\l r -> mrgReturn $ l * r))
    ]

instance FuncMapLike (MLOpCode a) (MListProgVal a) (MLFuncMap a) where
  getFuncMaybe (MLSOp o) (MLFuncMap m) = do
    r <- M.lookup o m
    case r of
      Left fu -> return fu
      Right _ -> Nothing
  getFuncMaybe (MLSOpConst o c) (MLFuncMap m) = do
    r <- M.lookup o m
    case r of
      Left _ -> Nothing
      Right f -> return $ f c
  getFunc o m = fromJust $ getFuncMaybe o m

newtype MLCFuncMap a = 
  MLCFuncMap (M.HashMap B.ByteString (Either (CFunc (CListProgVal a)) (a -> CFunc (CListProgVal a))))

mlcfuncMap :: (Num a, Ord a, Integral a) => MLCFuncMap a
mlcfuncMap = MLCFuncMap $
  M.fromList
    [ ( "intConst",
        Right $ \x -> CFunc 0 False $ \case
          [] -> return $ CLInt x
          _ -> throwError AssertionViolation
      ),
      ( "binCommLinear",
        Right $ \opc ->
          mlIntInt2IntUnaryCFunc True $ \l r -> intIntToIntCommLinearCFunction opc l r
      ),
      ("binMinus", Left $ mlIntInt2IntUnaryCFunc False $ \l r -> return $ l - r),
      ("binTimes", Left $ mlIntInt2IntUnaryCFunc True $ \l r -> return $ l * r),
      ("sum", Left $ mlList2IntUnaryCFunc $ return . sum),
      ("len", Left $ mlList2IntUnaryCFunc $ return . fromIntegral . length),
      ("head", Left $ mlList2IntUnaryCFunc $ return . head),
      ("last", Left $ mlList2IntUnaryCFunc $ return . last),
      ("access", Left $ mlIntList2IntBinaryCFunc (\i l -> return $ l !! fromIntegral i)),
      ( "count",
        Right $ \opc -> mlList2IntUnaryCFunc $ do
          foldM
            ( \acc va -> do
                r <- intToBoolCFunction opc va
                return $ if r then acc + 1 else acc
            )
            0
      ),
      ("min", Left $ mlList2IntUnaryCFunc $ return . foldl1' min),
      ("max", Left $ mlList2IntUnaryCFunc $ return . foldl1' max),
      ("neg", Left $ mlInt2IntUnaryCFunc $ return . negate),
      ("take", Left $ mlIntList2ListBinaryCFunc $ \i l ->
        if i < 0 || fromIntegral i >= length l then throwError AssertionViolation else
        return $ take (fromIntegral i) l),
      ("drop", Left $ mlIntList2ListBinaryCFunc $ \i l ->
        if i < 0 || fromIntegral i >= length l then throwError AssertionViolation else
        return $ drop (fromIntegral i) l),
      ("reverse", Left $ mlList2ListUnaryCFunc $ return . reverse),
      ("offset", Right $ \x -> mlList2ListUnaryCFunc $ \l -> return $ map (+x) l),
      ("negateList", Left $ mlList2ListUnaryCFunc $ \l -> return $ map negate l),
      ("filter", Right $ \opc -> mlList2ListUnaryCFunc $ \l -> filterM (intToBoolCFunction opc) l),
      ("zipCommLinear", Right $ \opc -> mlListList2ListBinaryCFunc $ \l r -> traverse (uncurry $ intIntToIntCommLinearCFunction opc) $ zip l r),
      ("zipMinus", Left $ mlListList2ListBinaryCFunc $ \l r -> traverse (\(l1, r1) -> return $ l1 - r1) $ zip l r),
      ("zipTimes", Left $ mlListList2ListBinaryCFunc $ \l r -> traverse (\(l1, r1) -> return $ l1 * r1) $ zip l r),
      ("scanlCommLinear", Right $ \opc -> mlList2ListUnaryCFunc $ scanlCFunc (intIntToIntCommLinearCFunction opc)),
      ("scanlMinus", Left $ mlList2ListUnaryCFunc $ scanlCFunc (\l r -> return $ l - r)),
      ("scanlTimes", Left $ mlList2ListUnaryCFunc $ scanlCFunc (\l r -> return $ l * r)),
      ("scanrCommLinear", Right $ \opc -> mlList2ListUnaryCFunc $ scanrCFunc (intIntToIntCommLinearCFunction opc)),
      ("scanrMinus", Left $ mlList2ListUnaryCFunc $ scanrCFunc (\l r -> return $ l - r)),
      ("scanrTimes", Left $ mlList2ListUnaryCFunc $ scanrCFunc (\l r -> return $ l * r))
    ]

instance CFuncMapLike (CMLOpCode a) (CListProgVal a) (MLCFuncMap a) where
  getCFuncMaybe (CMLSOp o) (MLCFuncMap m) = do
    r <- M.lookup o m
    case r of
      Left fu -> return fu
      Right _ -> Nothing
  getCFuncMaybe (CMLSOpConst o c) (MLCFuncMap m) = do
    r <- M.lookup o m
    case r of
      Left _ -> Nothing
      Right f -> return $ f c
  getCFunc o m = fromJust $ getCFuncMaybe o m
