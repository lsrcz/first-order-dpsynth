module OOPSLA.Gen where

import qualified Data.ByteString as B
import Grisette
import OOPSLA.Core
-- import Debug.Trace

data CombASTSpec0 sval = CombASTSpec0
  { unaryDepth :: Int,
    binaryDepth :: Int,
    ternaryDepth :: Int,
    unaries :: [B.ByteString],
    binaries :: [B.ByteString],
    ternaries :: [B.ByteString]
  }

data CombASTSpec sval = CombASTSpec
  { combSpec0 :: CombASTSpec0 sval,
    combArgs :: [Int]
  }

instance Mergeable sval => GenSym (CombASTSpec sval) (AST sval) where
  fresh :: forall m. (Mergeable sval, MonadFresh m) => CombASTSpec sval -> m (UnionM (AST sval))
  fresh (CombASTSpec spec args) = go (unaryDepth spec) (binaryDepth spec) (ternaryDepth spec)
    where
      currUnaries = unaries spec
      currBinaries = binaries spec
      currTernaries = ternaries spec
      argGen :: m (UnionM (AST sval))
      argGen = mrgFmap Arg . mrgReturn <$> chooseFresh args
      uGen :: Int -> m (UnionM (AST sval))
      uGen u
        | u <= 0 = argGen
        | otherwise = do
            uf <- chooseFresh currUnaries
            l <- uGen (u - 1)
            return $ mrgUnary uf l
      -- sp n = [(n - x, x) | x <- [0 .. n `div` 2]]
      go :: Int -> Int -> Int -> m (UnionM (AST sval))
      -- go :: Int -> Int -> m (UnionM (AST sval))
      go u b t
        | b <= 0 && t <= 0 = uGen u
        | b <= 0 = go3 u 0 t
        | t <= 0 = go2 u b 0
        | otherwise = do
          ba <- go2 u b t
          ta <- go3 u b t
          chooseUnionFresh [ba, ta]
      go2 :: Int -> Int -> Int -> m (UnionM (AST sval))
      go2 u b t = do
        tf <- chooseFresh currBinaries
        r <- (traverse . traverse) (uncurry (go u)) specs
        let r2 = (\[x, y] -> Binary tf x y) <$> r
        chooseFresh r2
        where
          specs = [[(b1, t1), (b2, t2)] | (b1, b2) <- split2 (b - 1), (t1, t2) <- split2 t]
      
      go3 :: Int -> Int -> Int -> m (UnionM (AST sval))
      go3 u b t = do
        tf <- chooseFresh currTernaries
        r <- (traverse . traverse) (uncurry (go u)) specs
        let r2 = (\[x, y, z] -> Ternary tf x y z) <$> r
        chooseFresh r2
        where
          specs = [[(b1, t1), (b2, t2), (b3, t3)] | (b1, b2, b3) <- split3 b, (t1, t2, t3) <- split30 (t - 1)]
      
      split2 :: Int -> [(Int, Int)]
      split2 n = [(a, b) | a <- [0..n], b <- [0..n], a + b == n, a <= b ]
      split30 :: Int -> [(Int, Int, Int)]
      split30 n = [(0, b, c) | b <- [0..n], c <- [0..n], b + c == n, b <= c ]
      split3 :: Int -> [(Int, Int, Int)]
      split3 n = [(a, b, c) | a <- [0..1], b <- [0..n], c <- [0..n], a + b + c == n, b <= c ]


data CombProgramSpec cval sval = CombProgramSpec
  { initsSpec :: [cval],
    updatesSpec :: CombASTSpec0 sval,
    terminateSpec :: CombASTSpec0 sval,
    slots :: Int,
    inputNumSpec :: Int
  }

instance (ToSym cval sval, SimpleMergeable sval) => GenSym (CombProgramSpec cval sval) (Program sval)

instance (ToSym cval sval, SimpleMergeable sval) => GenSymSimple (CombProgramSpec cval sval) (Program sval) where
  simpleFresh ::
    forall m.
    ( MonadFresh m
    ) =>
    CombProgramSpec cval sval ->
    m (Program sval)
  simpleFresh spec = do
    i <- initsGen
    u <- updatesGen
    t <- terminateGen
    return $ Program i u t (inputNumSpec spec)
    where
      initGen :: m sval
      initGen = chooseSimpleFresh $ toSym <$> initsSpec spec
      updateGen :: m (UnionM (AST sval))
      updateGen = fresh (CombASTSpec (updatesSpec spec) [0 .. slots spec + inputNumSpec spec - 1])
      terminateGen :: m (UnionM (AST sval))
      terminateGen = fresh (CombASTSpec (terminateSpec spec) [0 .. slots spec - 1])
      initsGen :: m [sval]
      initsGen = traverse (const initGen) [1 .. slots spec]
      updatesGen :: m [UnionM (AST sval)]
      updatesGen = traverse (const updateGen) [1 .. slots spec]

data ExtProgramSpec cval sval = ExtProgramSpec
  { extInitsSpec :: [cval],
    extsSpec :: CombASTSpec0 sval,
    extsOpt :: B.ByteString,
    extsExtNumEach :: Int,
    extsMaxSelect :: Int,
    extsSlots :: Int,
    extsInputNum :: Int
  }

instance (ToSym cval sval, SimpleMergeable sval) => GenSym (ExtProgramSpec cval sval) (Program sval)

instance (ToSym cval sval, SimpleMergeable sval) => GenSymSimple (ExtProgramSpec cval sval) (Program sval) where
  simpleFresh ::
    forall m.
    ( MonadFresh m
    ) =>
    ExtProgramSpec cval sval ->
    m (Program sval)
  simpleFresh spec = do
    i <- initsGen
    o <- optsGen
    t <- terGen [0 .. extsSlots spec - 1]
    return $ Program i o t (extsInputNum spec)
    where
      initGen :: m sval
      initGen = chooseSimpleFresh $ toSym <$> extInitsSpec spec
      initsGen :: m [sval]
      initsGen = traverse (const initGen) [1 .. extsSlots spec]
      extGen :: Int -> m (UnionM (AST sval))
      extGen i = fresh (CombASTSpec (extsSpec spec) ([0 .. extsInputNum spec - 1] ++ [i]))
      extsGen :: m [UnionM (AST sval)]
      extsGen = traverse extGen [extsInputNum spec .. extsInputNum spec + extsSlots spec - 1]

      allExtsGen :: Int -> m [UnionM (AST sval)]
      allExtsGen 0 = return []
      allExtsGen i = do
        x <- extsGen
        r <- allExtsGen (i - 1)
        return $ x ++ r

      optGen :: Int -> [UnionM (AST sval)] -> m (UnionM (AST sval))
      optGen i exts | i == 1 = chooseFresh $ NoMrg <$> exts
      optGen i exts = do
        l <- optGen (i - 1) exts
        r <- chooseFresh $ NoMrg <$> exts
        return $ mrgBinary (mrgReturn $ extsOpt spec) l r

      optsGen :: m [UnionM (AST sval)]
      optsGen = do
        allExts <- allExtsGen (extsExtNumEach spec)
        traverse (const $ optGen (extsMaxSelect spec) allExts) [1 .. extsSlots spec]
      {-
      allSelects :: [a] -> [[a]]
      allSelects [] = [[]]
      allSelects (x : xs) = concat [[x : y, y] | y <- allSelects xs]
      buildOpt :: [AST sval] -> AST sval
      buildOpt [] = undefined
      buildOpt [a] = a
      buildOpt (x : xs) = Binary (mrgReturn $ extsOpt spec) (mrgReturn x) $ mrgReturn (buildOpt xs)

      allExtsGen :: Int -> m [UnionM (AST sval)]
      allExtsGen 0 = return []
      allExtsGen i = do
        x <- extsGen
        r <- allExtsGen (i - 1)
        return $ x ++ r

      optGen :: [UnionM (AST sval)] -> m (UnionM (AST sval))
      optGen exts = do
        let m = filter (\x -> not (null x) && length x <= extsMaxSelect spec) $ allSelects $ NoMrg <$> exts
        let j = buildOpt <$> m
        chooseFresh j

      optsGen :: m [UnionM (AST sval)]
      optsGen = do
        allExts <- allExtsGen (extsExtNumEach spec)
        traverse (const $ optGen allExts) [1 .. extsSlots spec]
        -}

      terGen :: [Int] -> m (UnionM (AST sval))
      terGen [i] = return $ mrgArg $ mrgReturn i
      terGen (x : xs) = mrgBinary (mrgReturn $ extsOpt spec) (mrgArg $ mrgReturn x) <$> terGen xs
      terGen _ = undefined
