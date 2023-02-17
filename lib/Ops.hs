module Ops where

import Core
import qualified Data.HashMap.Strict as M
import Grisette

availableUnary :: (Num a, SimpleMergeable a) => UnaryFuncMap a
availableUnary =
  M.fromList
    [ ("zero", const $ mrgReturn 0),
      ("-", mrgReturn . negate),
      ("id", mrgReturn)
    ]

availableBinary :: (Num a, SOrd a, SimpleMergeable a) => BinaryFuncMap a
availableBinary =
  M.fromList
    [ ("+", \x y -> mrgReturn $ x + y),
      ("-", \x y -> mrgReturn $ x - y),
      ("-comp", \x y -> mrgReturn $ y - x),
      ("max", \x y -> mrgReturn $ mrgIte (x >=~ y :: SymBool) x y),
      ("min", \x y -> mrgReturn $ mrgIte (x >=~ y :: SymBool) y x)
    ]

noOverflowAvailableBinary :: (Num a, SOrd a, SimpleMergeable a) => BinaryFuncMap a
noOverflowAvailableBinary =
  M.fromList
    [ ( "+",
        \x y -> do
          let r = x + y
          symAssume $ (x >~ 0 &&~ y >~ 0) `implies` (r >~ 0)
          symAssume $ (x <~ 0 &&~ y <~ 0) `implies` (r <~ 0)
          mrgReturn r
      ),
      ( "-",
        \x y -> do
          let r = x - y
          symAssume $ (x >~ 0 &&~ y <~ 0) `implies` (r >~ 0)
          symAssume $ (x <~ 0 &&~ y >~ 0) `implies` (r <~ 0)
          mrgReturn r
      ),
      ( "-comp",
        \x y -> do
          let r = y - x
          symAssume $ (x >~ 0 &&~ y <~ 0) `implies` (r <~ 0)
          symAssume $ (x <~ 0 &&~ y >~ 0) `implies` (r >~ 0)
          mrgReturn r
      ),
      ( "max",
        \x y -> do
          let r = mrgIte (x >=~ y :: SymBool) x y
          symAssume $ r >=~ x
          symAssume $ r >=~ y
          mrgReturn r
      ),
      ( "min",
        \x y -> do
          let r = mrgIte (x >=~ y :: SymBool) y x
          symAssume $ r <=~ x
          symAssume $ r <=~ y
          mrgReturn r
      )
    ]
