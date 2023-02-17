module Core where

import Control.Monad.Except
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Char
import qualified Data.HashMap.Lazy as M
import Data.Hashable
import Data.List (intercalate)
import GHC.Generics
import Grisette

data ConAST val
  = ConArg Int
  | ConConst val
  | ConUnary B.ByteString (ConAST val)
  | ConBinary B.ByteString (ConAST val) (ConAST val)
  | ConNoMrg (ConAST val)
  deriving (Generic)

data AST val
  = Arg (UnionM Int)
  | Const (UnionM val)
  | Unary (UnionM B.ByteString) (UnionM (AST val))
  | Binary (UnionM B.ByteString) (UnionM (AST val)) (UnionM (AST val))
  | NoMrg (UnionM (AST val))
  deriving (Show, Generic, Eq, Hashable)
  deriving (EvaluateSym, SEq) via (Default (AST val))

deriving via
  (Default (ConAST cval))
  instance
    ToCon sval cval => ToCon (AST sval) (ConAST cval)

deriving via
  (Default (AST sval))
  instance
    (ToSym cval sval, Mergeable sval) => ToSym (ConAST cval) (AST sval)

instance Mergeable val => Mergeable (AST val) where
  rootStrategy =
    SortedStrategy
      ( \case
          Arg {} -> 0 :: Int
          Const {} -> 1
          Unary {} -> 2
          Binary {} -> 3
          NoMrg {} -> 4
      )
      ( \case
          0 -> SimpleStrategy $ \cond (Arg l) (Arg r) -> Arg $ mrgIf cond l r
          1 -> SimpleStrategy $ \cond (Const l) (Const r) -> Const $ mrgIf cond l r
          2 -> SimpleStrategy $ \cond (Unary lf l) (Unary rf r) ->
            Unary (mrgIf cond lf rf) (mrgIf cond l r)
          3 -> SimpleStrategy $ \cond (Binary lf ll lr) (Binary rf rl rr) ->
            Binary (mrgIf cond lf rf) (mrgIf cond ll rl) (mrgIf cond lr rr)
          4 -> NoStrategy
          _ -> undefined
      )

formatConAST :: (Show val) => Int -> String -> ConAST val -> String
formatConAST n idx (ConArg v)
  | v < n = chr (ord 'a' + v) : "[i]"
  | otherwise = 'p' : show (v - n + 1) ++ "[" ++ idx ++ "]"
formatConAST _ _ (ConConst v) = show v
formatConAST n idx (ConUnary f sub)
  | isAlpha (C.head f) = C.unpack f ++ "(" ++ formatConAST n idx sub ++ ")"
  | otherwise = "(" ++ C.unpack f ++ " " ++ formatConAST n idx sub ++ ")"
formatConAST n idx (ConBinary f l r)
  | isAlpha (C.head f) = C.unpack f ++ "(" ++ formatConAST n idx l ++ ", " ++ formatConAST n idx r ++ ")"
  | otherwise = "(" ++ formatConAST n idx l ++ " " ++ C.unpack f ++ " " ++ formatConAST n idx r ++ ")"
formatConAST n idx (ConNoMrg v) = formatConAST n idx v

data ConProgram val = ConProgram
  { cinits :: [val],
    cupdates :: [ConAST val],
    cterminate :: ConAST val,
    cinputNum :: Int
  }
  deriving (Generic)

data Program val = Program
  { inits :: [val],
    updates :: [UnionM (AST val)],
    terminate :: UnionM (AST val),
    inputNum :: Int
  }
  deriving (Show, Generic)
  deriving (EvaluateSym, SEq, Mergeable) via (Default (Program val))

deriving via
  (Default (ConProgram cval))
  instance
    ToCon sval cval => ToCon (Program sval) (ConProgram cval)

deriving via
  (Default (Program sval))
  instance
    (ToSym cval sval, Mergeable sval) => ToSym (ConProgram cval) (Program sval)

instance Show val => Show (ConProgram val) where
  show (ConProgram i u t a) =
    unlines $
      [ "def f("
          ++ intercalate
            ", "
            ((\x -> let nm = chr $ ord 'a' + x in nm : " = [" ++ [nm] ++ "1, ..., " ++ [nm] ++ "n]") <$> [0 .. a - 1])
          ++ "):"
      ]
        ++ fmap (\(n, _) -> "  p" ++ show n ++ " = array()") (zip [1 :: Int ..] i)
        ++ fmap (\(n, v) -> "  p" ++ show n ++ "[0] = " ++ show v) (zip [1 :: Int ..] i)
        ++ ["  for i from 1 to n:"]
        ++ fmap (\(n, v) -> "    p" ++ show n ++ "[i] = " ++ formatConAST a "i - 1" v) (zip [1 :: Int ..] u)
        ++ ["  return " ++ formatConAST 0 "n" t]

type UnaryFuncMap val = M.HashMap B.ByteString (val -> ExceptT VerificationConditions UnionM val)

type BinaryFuncMap val = M.HashMap B.ByteString (val -> val -> ExceptT VerificationConditions UnionM val)

$(makeUnionWrapper "mrg" ''AST)
