{-# LANGUAGE UndecidableInstances #-}

module Component.ListOps where

import Common.FuncMap
import Common.ListProg
import Common.T
import Component.Ops
import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as M
import Data.List
import Data.Maybe
import GHC.Generics
import Grisette
import Debug.Trace

listAuxList2IntUnaryFunc ::
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
listAuxList2IntUnaryFunc f = Func 1 False $ \case
  [a] -> do
    r <- liftToMonadUnion a
    case r of
      LIntList l -> mrgFmap (mrgReturn . LInt) $ f l
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

listAuxInt2IntUnaryFunc :: Mergeable si => (forall m. (MonadError VerificationConditions m, MonadUnion m) => si -> m si) -> Func (MListProgVal si)
listAuxInt2IntUnaryFunc f = Func 1 False $ \case
  [a] -> do
    r <- liftToMonadUnion a
    case r of
      LInt v -> mrgFmap (mrgReturn . LInt) $ f v
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

listAuxList2ListUnaryFunc :: Mergeable si => (forall m. (MonadError VerificationConditions m, MonadUnion m, MonadFresh m) => [si] -> m [si]) -> Func (MListProgVal si)
listAuxList2ListUnaryFunc f = Func 1 False $ \case
  [a] -> do
    r <- liftToMonadUnion a
    case r of
      LIntList v -> mrgFmap (mrgReturn . LIntList) $ f v
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

listAuxIntInt2IntUnaryFunc ::
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
listAuxIntInt2IntUnaryFunc comm f = Func 2 comm $ \case
  [v1, v2] -> do
    v1' <- liftToMonadUnion v1
    v2' <- liftToMonadUnion v2
    case (v1', v2') of
      (LInt i1, LInt i2) -> mrgFmap (mrgReturn . LInt) $ f i1 i2
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

listAuxIntList2IntBinaryFunc ::
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
listAuxIntList2IntBinaryFunc f = Func 2 False $ \case
  [v1, v2] -> do
    v1' <- liftToMonadUnion v1
    v2' <- liftToMonadUnion v2
    case (v1', v2') of
      (LInt i1, LIntList i2) -> mrgFmap (mrgReturn . LInt) $ f i1 i2
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

listAuxIntList2ListBinaryFunc ::
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
listAuxIntList2ListBinaryFunc f = Func 2 False $ \case
  [v1, v2] -> do
    v1' <- liftToMonadUnion v1
    v2' <- liftToMonadUnion v2
    case (v1', v2') of
      (LInt i1, LIntList i2) -> mrgFmap (mrgReturn . LIntList) $ f i1 i2
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

listAuxListList2ListBinaryFunc ::
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
listAuxListList2ListBinaryFunc f = Func 2 False $ \case
  [v1, v2] -> do
    v1' <- liftToMonadUnion v1
    v2' <- liftToMonadUnion v2
    case (v1', v2') of
      (LIntList i1, LIntList i2) -> mrgFmap (mrgReturn . LIntList) $ f i1 i2
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

---- CFunc ----
listAuxList2IntUnaryCFunc ::
  ( [ci] ->
    Either VerificationConditions ci
  ) ->
  CFunc (CListProgVal ci)
listAuxList2IntUnaryCFunc f = CFunc 1 False $ \case
  [a] -> do
    case a of
      CLIntList l -> CLInt <$> f l
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

listAuxInt2IntUnaryCFunc :: (ci -> Either VerificationConditions ci) -> CFunc (CListProgVal ci)
listAuxInt2IntUnaryCFunc f = CFunc 1 False $ \case
  [a] -> do
    case a of
      CLInt v -> CLInt <$> f v
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

listAuxList2ListUnaryCFunc :: ([ci] -> Either VerificationConditions [ci]) -> CFunc (CListProgVal ci)
listAuxList2ListUnaryCFunc f = CFunc 1 False $ \case
  [a] -> do
    case a of
      CLIntList v -> CLIntList <$> f v
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

listAuxIntInt2IntUnaryCFunc ::
  Bool ->
  ( ci ->
    ci ->
    Either VerificationConditions ci
  ) ->
  CFunc (CListProgVal ci)
listAuxIntInt2IntUnaryCFunc comm f = CFunc 2 comm $ \case
  [v1, v2] -> do
    case (v1, v2) of
      (CLInt i1, CLInt i2) -> CLInt <$> f i1 i2
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

listAuxIntList2IntBinaryCFunc ::
  ( ci ->
    [ci] ->
    Either VerificationConditions ci
  ) ->
  CFunc (CListProgVal ci)
listAuxIntList2IntBinaryCFunc f = CFunc 2 False $ \case
  [v1, v2] -> do
    case (v1, v2) of
      (CLInt i1, CLIntList i2) -> CLInt <$> f i1 i2
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

listAuxIntList2ListBinaryCFunc ::
  ( ci ->
    [ci] ->
    Either VerificationConditions [ci]
  ) ->
  CFunc (CListProgVal ci)
listAuxIntList2ListBinaryCFunc f = CFunc 2 False $ \case
  [v1, v2] -> do
    case (v1, v2) of
      (CLInt i1, CLIntList i2) -> CLIntList <$> f i1 i2
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

listAuxListList2ListBinaryCFunc ::
  ( [ci] ->
    [ci] ->
    Either VerificationConditions [ci]
  ) ->
  CFunc (CListProgVal ci)
listAuxListList2ListBinaryCFunc f = CFunc 2 False $ \case
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

intIntToIntComlistAuxinearFunction ::
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
intIntToIntComlistAuxinearFunction opc v1 v2 =
  mrgIf (opc ==~ 0) (mrgReturn $ v1 + v2) $
    mrgIf (opc ==~ 1) (mrgReturn $ symMin v1 v2) (mrgReturn $ symMax v1 v2)

intToBoolCFunction :: (Ord ci, Num ci, Integral ci) => ci -> ci -> Either VerificationConditions Bool
intToBoolCFunction opc v =
  case opc of
    0 -> return $ v > 0
    1 -> return $ v < 0
    2 -> return $ even v
    _ -> return $ odd v

intIntToIntComlistAuxinearCFunction ::
  (Ord ci, Num ci) =>
  ci ->
  ci ->
  ci ->
  Either VerificationConditions ci
intIntToIntComlistAuxinearCFunction opc v1 v2 =
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
filterFunc opc (x : xs) = do
  curr <- intToBoolFunction opc x
  remaining <- filterFunc opc xs
  mrgIf curr (mrgReturn $ x : remaining) (mrgReturn remaining)

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
zipFunc f (x : xs) (y : ys) = do
  curr <- f x y
  remaining <- zipFunc f xs ys
  mrgReturn $ curr : remaining

zipComlistAuxinearFunc ::
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
zipComlistAuxinearFunc opc = zipFunc (intIntToIntComlistAuxinearFunction opc)

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
scanlFunc f (x : xs) = go x xs
  where
    go acc [] = mrgReturn [acc]
    go acc (y : ys) = do
      nextAcc <- f acc y
      rest <- go nextAcc ys
      mrgReturn (acc : rest)

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
scanlCFunc f (x : xs) = go x xs
  where
    go acc [] = return [acc]
    go acc (y : ys) = do
      nextAcc <- f acc y
      rest <- go nextAcc ys
      return (acc : rest)

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

newtype MLFuncMap a
  = MLFuncMap (M.HashMap B.ByteString (Either (Func (MListProgVal a)) (a -> Func (MListProgVal a))))

listAuxfuncMap :: (Num a, SOrd a, SimpleMergeable a, GenSymSimple () a) => MLFuncMap a
listAuxfuncMap =
  MLFuncMap $
    M.fromList
      [ ( "intConst",
          Right $ \x -> Func 0 False $ \case
            [] -> mrgReturn $ mrgReturn $ LInt x
            _ -> mrgThrowError AssertionViolation
        ),
        ( "binCommLinear",
          Right $ \opc ->
            listAuxIntInt2IntUnaryFunc True $ \l r -> intIntToIntComlistAuxinearFunction opc l r
        ),
        ("binMinus", Left $ listAuxIntInt2IntUnaryFunc False $ \l r -> mrgReturn $ l - r),
        ("binTimes", Left $ listAuxIntInt2IntUnaryFunc True $ \l r -> mrgReturn $ l * r),
        ("sum", Left $ listAuxList2IntUnaryFunc $ mrgReturn . sum),
        ("len", Left $ listAuxList2IntUnaryFunc $ mrgReturn . fromIntegral . length),
        ("head", Left $ listAuxList2IntUnaryFunc $ mrgReturn . head),
        ("last", Left $ listAuxList2IntUnaryFunc $ mrgReturn . last),
        ("access", Left $ listAuxIntList2IntBinaryFunc access),
        ( "count",
          Right $ \opc -> listAuxList2IntUnaryFunc $ do
            foldM
              ( \acc va -> do
                  r <- intToBoolFunction opc va
                  mrgReturn $ mrgIte r (acc + 1) acc
              )
              0
        ),
        ("min", Right $ \inf -> listAuxList2IntUnaryFunc $ mrgReturn . foldl' symMin inf),
        ("max", Right $ \ninf -> listAuxList2IntUnaryFunc $ mrgReturn . foldl' symMax ninf),
        ("neg", Left $ listAuxInt2IntUnaryFunc $ mrgReturn . negate),
        ("take", Left $ listAuxIntList2ListBinaryFunc takeFunc),
        ("drop", Left $ listAuxIntList2ListBinaryFunc dropFunc),
        ("reverse", Left $ listAuxList2ListUnaryFunc $ mrgReturn . reverse),
        ("offset", Right $ \x -> listAuxList2ListUnaryFunc $ \l -> mrgReturn $ map (+ x) l),
        ("negateList", Left $ listAuxList2ListUnaryFunc $ \l -> mrgReturn $ map negate l),
        ("filter", Right $ \opc -> listAuxList2ListUnaryFunc $ \l -> filterFunc opc l),
        ("zipCommLinear", Right $ \opc -> listAuxListList2ListBinaryFunc $ zipFunc (intIntToIntComlistAuxinearFunction opc)),
        ("zipMinus", Left $ listAuxListList2ListBinaryFunc $ zipFunc $ \l r -> mrgReturn $ l - r),
        ("zipTimes", Left $ listAuxListList2ListBinaryFunc $ zipFunc $ \l r -> mrgReturn $ l * r),
        ("scanlCommLinear", Right $ \opc -> listAuxList2ListUnaryFunc $ scanlFunc (intIntToIntComlistAuxinearFunction opc)),
        ("scanlMinus", Left $ listAuxList2ListUnaryFunc $ scanlFunc (\l r -> mrgReturn $ l - r)),
        ("scanlTimes", Left $ listAuxList2ListUnaryFunc $ scanlFunc (\l r -> mrgReturn $ l * r)),
        ("scanrCommLinear", Right $ \opc -> listAuxList2ListUnaryFunc $ scanrFunc (intIntToIntComlistAuxinearFunction opc)),
        ("scanrMinus", Left $ listAuxList2ListUnaryFunc $ scanrFunc (\l r -> mrgReturn $ l - r)),
        ("scanrTimes", Left $ listAuxList2ListUnaryFunc $ scanrFunc (\l r -> mrgReturn $ l * r))
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

newtype MLCFuncMap a
  = MLCFuncMap (M.HashMap B.ByteString (Either (CFunc (CListProgVal a)) (a -> CFunc (CListProgVal a))))

listAuxcfuncMap :: (Num a, Ord a, Integral a) => MLCFuncMap a
listAuxcfuncMap =
  MLCFuncMap $
    M.fromList
      [ ( "intConst",
          Right $ \x -> CFunc 0 False $ \case
            [] -> return $ CLInt x
            _ -> throwError AssertionViolation
        ),
        ( "binCommLinear",
          Right $ \opc ->
            listAuxIntInt2IntUnaryCFunc True $ \l r -> intIntToIntComlistAuxinearCFunction opc l r
        ),
        ("binMinus", Left $ listAuxIntInt2IntUnaryCFunc False $ \l r -> return $ l - r),
        ("binTimes", Left $ listAuxIntInt2IntUnaryCFunc True $ \l r -> return $ l * r),
        ("sum", Left $ listAuxList2IntUnaryCFunc $ return . sum),
        ("len", Left $ listAuxList2IntUnaryCFunc $ return . fromIntegral . length),
        ("head", Left $ listAuxList2IntUnaryCFunc $ return . head),
        ("last", Left $ listAuxList2IntUnaryCFunc $ return . last),
        ("access", Left $ listAuxIntList2IntBinaryCFunc (\i l -> return $ l !! fromIntegral i)),
        ( "count",
          Right $ \opc -> listAuxList2IntUnaryCFunc $ do
            foldM
              ( \acc va -> do
                  r <- intToBoolCFunction opc va
                  return $ if r then acc + 1 else acc
              )
              0
        ),
        ("min", Right $ \inf -> listAuxList2IntUnaryCFunc $ return . foldl' min inf),
        ("max", Right $ \ninf -> listAuxList2IntUnaryCFunc $ return . foldl' max ninf),
        ("neg", Left $ listAuxInt2IntUnaryCFunc $ return . negate),
        ( "take",
          Left $ listAuxIntList2ListBinaryCFunc $ \i l ->
            if i < 0 || fromIntegral i >= length l
              then throwError AssertionViolation
              else return $ take (fromIntegral i) l
        ),
        ( "drop",
          Left $ listAuxIntList2ListBinaryCFunc $ \i l ->
            if i < 0 || fromIntegral i >= length l
              then throwError AssertionViolation
              else return $ drop (fromIntegral i) l
        ),
        ("reverse", Left $ listAuxList2ListUnaryCFunc $ return . reverse),
        ("offset", Right $ \x -> listAuxList2ListUnaryCFunc $ \l -> return $ map (+ x) l),
        ("negateList", Left $ listAuxList2ListUnaryCFunc $ \l -> return $ map negate l),
        ("filter", Right $ \opc -> listAuxList2ListUnaryCFunc $ \l -> filterM (intToBoolCFunction opc) l),
        ("zipCommLinear", Right $ \opc -> listAuxListList2ListBinaryCFunc $ \l r -> traverse (uncurry $ intIntToIntComlistAuxinearCFunction opc) $ zip l r),
        ("zipMinus", Left $ listAuxListList2ListBinaryCFunc $ \l r -> traverse (\(l1, r1) -> return $ l1 - r1) $ zip l r),
        ("zipTimes", Left $ listAuxListList2ListBinaryCFunc $ \l r -> traverse (\(l1, r1) -> return $ l1 * r1) $ zip l r),
        ("scanlCommLinear", Right $ \opc -> listAuxList2ListUnaryCFunc $ scanlCFunc (intIntToIntComlistAuxinearCFunction opc)),
        ("scanlMinus", Left $ listAuxList2ListUnaryCFunc $ scanlCFunc (\l r -> return $ l - r)),
        ("scanlTimes", Left $ listAuxList2ListUnaryCFunc $ scanlCFunc (\l r -> return $ l * r)),
        ("scanrCommLinear", Right $ \opc -> listAuxList2ListUnaryCFunc $ scanrCFunc (intIntToIntComlistAuxinearCFunction opc)),
        ("scanrMinus", Left $ listAuxList2ListUnaryCFunc $ scanrCFunc (\l r -> return $ l - r)),
        ("scanrTimes", Left $ listAuxList2ListUnaryCFunc $ scanrCFunc (\l r -> return $ l * r))
      ]

instance Show a => CFuncMapLike (CMLOpCode a) (CListProgVal a) (MLCFuncMap a) where
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

newtype MLCombFuncMap a
  = MLCombFuncMap (M.HashMap B.ByteString (Either (Func (MT a)) (a -> Func (MT a))))

listCombUnaryFunc ::
  Mergeable si =>
  (T si -> Maybe a) ->
  (b -> T si) ->
  ( forall m.
    ( MonadError VerificationConditions m,
      MonadUnion m,
      MonadFresh m
    ) =>
    a ->
    m b
  ) ->
  Func (MT si)
listCombUnaryFunc e1 c f = Func 1 False $ \case
  [v1] -> do
    v1' <- liftToMonadUnion v1
    case e1 v1' of
      Just i1 -> mrgFmap (mrgReturn . c) $ f i1
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

listCombBinFunc ::
  Mergeable si =>
  (T si -> Maybe a) ->
  (T si -> Maybe b) ->
  (c -> T si) ->
  Bool ->
  ( forall m.
    ( MonadError VerificationConditions m,
      MonadUnion m,
      MonadFresh m
    ) =>
    a ->
    b ->
    m c
  ) ->
  Func (MT si)
listCombBinFunc e1 e2 c comm f = Func 2 comm $ \case
  [v1, v2] -> do
    v1' <- liftToMonadUnion v1
    v2' <- liftToMonadUnion v2
    case (e1 v1', e2 v2') of
      (Just i1, Just i2) -> mrgFmap (mrgReturn . c) $ f i1 i2
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

listCombTernaryFunc ::
  Mergeable si =>
  (T si -> Maybe a) ->
  (T si -> Maybe b) ->
  (T si -> Maybe c) ->
  (d -> T si) ->
  ( forall m.
    ( MonadError VerificationConditions m,
      MonadUnion m,
      MonadFresh m
    ) =>
    a ->
    b ->
    c ->
    m d
  ) ->
  Func (MT si)
listCombTernaryFunc e1 e2 e3 c f = Func 2 False $ \case
  [v1, v2, v3] -> do
    v1' <- liftToMonadUnion v1
    v2' <- liftToMonadUnion v2
    v3' <- liftToMonadUnion v3
    case (e1 v1', e2 v2', e3 v3') of
      (Just i1, Just i2, Just i3) -> mrgFmap (mrgReturn . c) $ f i1 i2 i3
      _ -> mrgThrowError AssertionViolation
  _ -> mrgThrowError AssertionViolation

listCombfuncMap :: (Num a, SOrd a, SimpleMergeable a, GenSymSimple () a) => MLCombFuncMap a
listCombfuncMap =
  MLCombFuncMap $
    M.fromList
      [ ( "intConst",
          Right $ \x -> Func 0 False $ \case
            [] -> mrgReturn $ mrgReturn $ TInt x
            _ -> mrgThrowError AssertionViolation
        ),
        ("binPlus", Left $ listCombBinFunc extTInt extTInt TInt True $ \l r -> mrgReturn $ l + r),
        ("binMinus", Left $ listCombBinFunc extTInt extTInt TInt False $ \l r -> mrgReturn $ l - r),
        ("binTimes", Left $ listCombBinFunc extTInt extTInt TInt True $ \l r -> mrgReturn $ l * r),
        ("ite", Left $ listCombTernaryFunc extTBool extTInt extTInt TInt $ \c l r -> mrgReturn $ mrgIte c l r),
        ("not", Left $ listCombUnaryFunc extTBool TBool $ mrgReturn . nots),
        ("and", Left $ listCombBinFunc extTBool extTBool TBool True $ \l r -> mrgReturn $ l &&~ r),
        ("or", Left $ listCombBinFunc extTBool extTBool TBool True $ \l r -> mrgReturn $ l ||~ r),
        ("leq", Left $ listCombBinFunc extTInt extTInt TBool False $ \l r -> mrgReturn $ l <=~ r),
        ("eq", Left $ listCombBinFunc extTInt extTInt TBool False $ \l r -> mrgReturn $ l ==~ r),
        ("max", Left $ listCombBinFunc extTInt extTInt TInt True $ \l r -> mrgReturn $ symMax l r),
        ("min", Left $ listCombBinFunc extTInt extTInt TInt True $ \l r -> mrgReturn $ symMin l r)
      ]

instance FuncMapLike (MLOpCode a) (MT a) (MLCombFuncMap a) where
  getFuncMaybe (MLSOp o) (MLCombFuncMap m) = do
    r <- M.lookup o m
    case r of
      Left fu -> return fu
      Right _ -> Nothing
  getFuncMaybe (MLSOpConst o c) (MLCombFuncMap m) = do
    r <- M.lookup o m
    case r of
      Left _ -> Nothing
      Right f -> return $ f c
  getFunc o m = fromJust $ getFuncMaybe o m

newtype MLCombCFuncMap a
  = MLCombCFuncMap (M.HashMap B.ByteString (Either (CFunc (CT a)) (a -> CFunc (CT a))))

listCombUnaryCFunc ::
  (CT si -> Maybe a) ->
  (b -> CT si) ->
  ( a ->
    Either VerificationConditions b
  ) ->
  CFunc (CT si)
listCombUnaryCFunc e1 c f = CFunc 1 False $ \case
  [v1] -> do
    case e1 v1 of
      Just i1 -> c <$> f i1
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

listCombBinCFunc ::
  (CT si -> Maybe a) ->
  (CT si -> Maybe b) ->
  (c -> CT si) ->
  Bool ->
  (
    a ->
    b ->
    Either VerificationConditions c
  ) ->
  CFunc (CT si)
listCombBinCFunc e1 e2 c comm f = CFunc 2 comm $ \case
  [v1, v2] -> do
    case (e1 v1, e2 v2) of
      (Just i1, Just i2) -> c <$> f i1 i2
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

listCombTernaryCFunc ::
  (CT si -> Maybe a) ->
  (CT si -> Maybe b) ->
  (CT si -> Maybe c) ->
  (d -> CT si) ->
  ( a ->
    b ->
    c ->
    Either VerificationConditions d
  ) ->
  CFunc (CT si)
listCombTernaryCFunc e1 e2 e3 c f = CFunc 2 False $ \case
  [v1, v2, v3] -> do
    case (e1 v1, e2 v2, e3 v3) of
      (Just i1, Just i2, Just i3) -> c <$> f i1 i2 i3
      _ -> throwError AssertionViolation
  _ -> throwError AssertionViolation

listCombcfuncMap :: (Num a, Ord a) => MLCombCFuncMap a
listCombcfuncMap = MLCombCFuncMap $
  M.fromList [
    ("intConst", Right $ \x -> CFunc 0 False $ \case
          [] -> return $ CInt x
          _ -> throwError AssertionViolation
      ),
    ("binPlus", Left $ listCombBinCFunc extCTInt extCTInt CInt True $ \l r -> return $ l + r),
    ("binMinus", Left $ listCombBinCFunc extCTInt extCTInt CInt False $ \l r -> return $ l - r),
    ("binTimes", Left $ listCombBinCFunc extCTInt extCTInt CInt True $ \l r -> return $ l * r),
    ("ite", Left $ listCombTernaryCFunc extCTBool extCTInt extCTInt CInt $ \c l r -> return $ if c then l else r),
    ("not", Left $ listCombUnaryCFunc extCTBool CBool $ return . not),
    ("and", Left $ listCombBinCFunc extCTBool extCTBool CBool True $ \l r -> return $ l && r),
    ("or", Left $ listCombBinCFunc extCTBool extCTBool CBool True $ \l r -> return $ l || r),
    ("leq", Left $ listCombBinCFunc extCTInt extCTInt CBool False $ \l r -> return $ l <= r),
    ("eq", Left $ listCombBinCFunc extCTInt extCTInt CBool False $ \l r -> return $ l == r),
    ("max", Left $ listCombBinCFunc extCTInt extCTInt CInt True $ \l r -> return $ max l r),
    ("min", Left $ listCombBinCFunc extCTInt extCTInt CInt True $ \l r -> return $ min l r)
  ]

instance CFuncMapLike (CMLOpCode a) (CT a) (MLCombCFuncMap a) where
  getCFuncMaybe (CMLSOp o) (MLCombCFuncMap m) = do
    r <- M.lookup o m
    case r of
      Left fu -> return fu
      Right _ -> Nothing
  getCFuncMaybe (CMLSOpConst o c) (MLCombCFuncMap m) = do
    r <- M.lookup o m
    case r of
      Left _ -> Nothing
      Right f -> return $ f c
  getCFunc o m = fromJust $ getCFuncMaybe o m
