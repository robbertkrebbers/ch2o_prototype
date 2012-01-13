{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XGADTs #-}
{-# OPTIONS -XKindSignatures #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XUndecidableInstances #-}
{-# OPTIONS -XFlexibleContexts #-}
{-# OPTIONS -XStandaloneDeriving #-}
{-# OPTIONS -XFunctionalDependencies #-}

module Expressions where

import Util
import Types
import Values
import SimpleMemory
import Pointers
import RLValues
import Memory

import Prelude
import Data.Bits
import Control.Monad
import Control.Monad.Maybe
import Control.Monad.State
import Control.Applicative

{- Manipulation of values -}
castB :: EnvReader m => RBVal -> BType -> MaybeT m RBVal
castB (VPointer p) (TPointer τ) = VPointer <$> maybeT (pCast p τ)
castB (VNULL _)    (TPointer τ) = return (VNULL τ)
castB v            τ            = guard (bTypeOf v == τ) >> return v

cast :: EnvReader m => RVal -> Type -> MaybeT m RVal
cast (VBase _ v) (TBase _ τ) = VBase False <$> castB v τ
cast _           _           = nothingT

{- Operations -}
data BinOp = PlusOp | MinusOp | MultOp | DivOp | RemOp | ShiftLOp | ShiftROp |
  LeOp | LtOp | GeOp | GtOp | EqOp | NeOp |
  BitAndOp | BitOrOp | BitXorOp deriving (Eq, Show)
data UnOp = NotOp | CompOp | NegOp deriving (Eq, Show)

boolToInt :: Bool -> Integer
boolToInt b = if b then 1 else 0

intToBool :: Integer -> Bool
intToBool = (0 /=)

evalUnOpInt :: UnOp -> Integer -> Maybe Integer
evalUnOpInt CompOp x = Just (complement x)
evalUnOpInt NegOp  x = Just (negate x)
evalUnOpInt NotOp  x = Just (boolToInt (not (intToBool x)))

evalBinOpInt :: BinOp -> Integer -> Integer-> Maybe Integer
evalBinOpInt NeOp     x y = Just (if x /= y then 1 else 0)
evalBinOpInt GeOp     x y = Just (if y <= x then 1 else 0)
evalBinOpInt GtOp     x y = Just (if y < x then 1 else 0)
evalBinOpInt EqOp     x y = Just (if x == y then 1 else 0)
evalBinOpInt LeOp     x y = Just (if x <= y then 1 else 0)
evalBinOpInt LtOp     x y = Just (if x < y then 1 else 0)
evalBinOpInt PlusOp   x y = Just (x + y)
evalBinOpInt MinusOp  x y = Just (x - y)
evalBinOpInt MultOp   x y = Just (x * y)
evalBinOpInt DivOp    x y = Just (x `quot` y)
evalBinOpInt RemOp    x y = Just (x `rem` y)
evalBinOpInt ShiftLOp x y = Just (x `shiftL` fromEnum y)
evalBinOpInt ShiftROp x y = Just (x `shiftR` fromEnum y)
evalBinOpInt BitAndOp x y = Just (x .&. y)
evalBinOpInt BitOrOp  x y = Just (x .|. y)
evalBinOpInt BitXorOp x y = Just (x `xor` y)

boolToValB :: Bool -> BVal a
boolToValB = VInt . boolToInt

vFalse :: BVal a
vFalse = boolToValB False

vTrue :: BVal a
vTrue = boolToValB True

valToBoolB :: BVal a -> Maybe Bool
valToBoolB (VInt x)     = Just (intToBool x)
valToBoolB (VNULL _)    = Just False
valToBoolB (VPointer _) = Just True
valToBoolB _            = Nothing

valToBool :: RVal -> Maybe Bool
valToBool (VBase _ v) = valToBoolB v
valToBool _           = Nothing

negateVal :: BVal a -> Maybe (BVal a)
negateVal v = boolToValB <$> not <$> valToBoolB v

evalUnOpB :: MemReader m => UnOp -> BVal a -> MaybeT m (BVal a)
evalUnOpB op    (VInt x) = maybeT (VInt <$> evalUnOpInt op x)
evalUnOpB NotOp v        = maybeT (negateVal v)
evalUnOpB _     _        = nothingT

evalUnOp :: MemReader m => UnOp -> RVal -> MaybeT m RVal
evalUnOp op (VBase _ v) = VBase False <$> evalUnOpB op v
evalUnOp _  _           = nothingT

typeBinOpB :: BinOp -> BType -> BType -> Maybe BType
typeBinOpB NeOp    τ1            τ2            = typeBinOpB EqOp τ1 τ2
typeBinOpB GeOp    τ1            τ2            = typeBinOpB LeOp τ2 τ1
typeBinOpB GtOp    τ1            τ2            = typeBinOpB LtOp τ2 τ1
typeBinOpB _       TInt          TInt          = Just TInt
typeBinOpB PlusOp  (TPointer τ)  TInt          = Just (TPointer τ)
typeBinOpB PlusOp  TInt          (TPointer τ)  = Just (TPointer τ)
typeBinOpB MinusOp (TPointer τ1) (TPointer τ2) = guard (τ1 == τ2) >> Just TInt
typeBinOpB EqOp    (TPointer τ1) (TPointer τ2) = guard (τ1 == τ2) >> Just (TPointer τ1)
typeBinOpB LeOp    (TPointer τ1) (TPointer τ2) = guard (τ1 == τ2) >> Just (TPointer τ1)
typeBinOpB LtOp    (TPointer τ1) (TPointer τ2) = guard (τ1 == τ2) >> Just (TPointer τ1)
typeBinOpB _       _             _             = Nothing

typeBinOp :: BinOp -> Type -> Type -> Maybe Type
typeBinOp op (TBase _ τ1) (TBase _ τ2) = TBase False <$> typeBinOpB op τ1 τ2
typeBinOp _  _            _            = Nothing

evalBinOpB :: MemReader m => BinOp -> RBVal -> RBVal-> MaybeT m RBVal
evalBinOpB op      (VInt x)      (VInt y)      = maybeT (VInt <$> evalBinOpInt op x y)
evalBinOpB NeOp    v1            v2            = evalBinOpB EqOp v1 v2 >>= maybeT . negateVal
evalBinOpB GeOp    v1            v2            = evalBinOpB LeOp v2 v1
evalBinOpB GtOp    v1            v2            = evalBinOpB LtOp v2 v1
evalBinOpB PlusOp  (VInt x)      (VPointer p)  = maybeT (VPointer <$> pPlus (fromEnum x) p)
evalBinOpB PlusOp  (VPointer p)  (VInt x)      = maybeT (VPointer <$> pPlus (fromEnum x) p)
evalBinOpB MinusOp (VPointer p1) (VPointer p2) = maybeT (VInt <$> toEnum <$> pMinus p1 p2)
evalBinOpB MinusOp (VNULL _)     (VNULL _)     = return (VInt 0)
evalBinOpB EqOp    (VPointer _)  (VNULL _)     = return vFalse
evalBinOpB EqOp    (VNULL _)     (VPointer _)  = return vFalse
evalBinOpB EqOp    (VPointer p1) (VPointer p2) = boolToValB <$> (p1 ==? p2)
evalBinOpB EqOp    (VNULL _)     (VNULL _)     = return vTrue
evalBinOpB LeOp    (VPointer p1) (VPointer p2) = boolToValB <$> (p1 <=? p2)
evalBinOpB LeOp    (VNULL _)     (VNULL _)     = return vTrue
evalBinOpB LtOp    (VPointer p1) (VPointer p2) = boolToValB <$> (p1 <? p2)
evalBinOpB LtOp    (VNULL _)     (VNULL _)     = return vFalse
evalBinOpB _       _              _            = nothingT

evalBinOp :: MemReader m => BinOp -> RVal -> RVal-> MaybeT m RVal
evalBinOp op (VBase _ v1) (VBase _ v2) = VBase False <$> evalBinOpB op v1 v2
evalBinOp _  _            _            = nothingT

{- Expressions -}
data Expr :: * -> * where
  -- type expressions
  VLType    :: Type -> VLType
  VLPointer :: Bool -> VLType -> VLType
  VLArray   :: VLType -> RExpr -> VLType
  -- right expressions
  EVal      :: RVal -> RExpr
  ECall     :: Id -> [RExpr] -> RExpr
  EAssign   :: LExpr -> RExpr -> RExpr
  EToVal    :: LExpr -> RExpr
  EAddrOf   :: LExpr -> RExpr
  EField    :: StructUnion -> Int -> RExpr -> RExpr
  EBinOp    :: BinOp -> RExpr -> RExpr -> RExpr
  EUnOp     :: UnOp -> RExpr -> RExpr
  EPreOp    :: BinOp -> LExpr -> RExpr -> RExpr
  EPostOp   :: BinOp -> LExpr -> RExpr -> RExpr
  ECast     :: VLType -> RExpr -> RExpr
  EIf       :: RExpr -> RExpr -> RExpr -> RExpr
  EComma    :: RExpr -> RExpr -> RExpr
  -- left expressions
  ELVal     :: LVal -> LExpr
  EVar      :: Id -> LExpr
  EDeref    :: RExpr -> LExpr
  ELField   :: StructUnion -> Int -> LExpr -> LExpr

type VLType = Expr Type
type RExpr  = Expr RVal
type LExpr  = Expr LVal

deriving instance Eq (Expr a)
deriving instance Show (Expr a)

eMap :: (Type -> Type) -> (RVal -> RVal) -> (LVal -> LVal) -> Expr a -> Expr a
eMap ft fv fl = m
 where
  m :: Expr a -> Expr a
  m (VLType τ)        = VLType (ft τ)
  m (VLPointer c τ)   = VLPointer c (m τ)
  m (VLArray τ r)     = VLArray (m τ) (m r)
  m (EVal v)          = EVal (fv v)
  m (ECall x rs)      = ECall x (m <$> rs)
  m (EAssign l r)     = EAssign (m l) (m r)
  m (EToVal l)        = EToVal (m l)
  m (EAddrOf l)       = EAddrOf (m l)
  m (EField su i r)   = EField su i (m r)
  m (EBinOp op r1 r2) = EBinOp op (m r1) (m r2)
  m (EPreOp op l r)   = EPreOp op (m l) (m r)
  m (EPostOp op l r)  = EPostOp op (m l) (m r)
  m (EUnOp op r)      = EUnOp op (m r)
  m (ECast τ r)       = ECast (m τ) (m r)
  m (EIf r1 r2 r3)    = EIf (m r1) (m r2) (m r3)
  m (EComma r1 r2)    = EComma (m r1) (m r2)
  m (ELVal l)         = ELVal (fl l)
  m (EVar x)          = EVar x
  m (EDeref r)        = EDeref (m r)
  m (ELField su i l)  = ELField su i (m l)

constExpr :: MemReader m => (Id -> MaybeT m Block) -> Expr a -> MaybeT m a
constExpr _ (VLType a)        = return a
constExpr f (VLPointer c τ)   = TBase c . TPointer <$> constExpr f τ
constExpr f (VLArray τvl r)   = do
  τ <- constExpr f τvl
  VBase _ (VInt n) <- constExpr f r
  guard (n >= 1)
  return (TArray τ (fromEnum n))
constExpr _ (EVal a)          = return a
constExpr f (EToVal l)        = do
  Pointer a τa i (TArray τ _) <- constExpr f l
  return (VBase False (VPointer (Pointer a τa i τ)))
constExpr f (EAddrOf l)       = VBase False . VPointer <$> constExpr f l
constExpr f (EBinOp op r1 r2) = do
  v1 <- constExpr f r1
  v2 <- constExpr f r2
  evalBinOp op v1 v2
constExpr f (EUnOp op r)      = do
  v <- constExpr f r
  evalUnOp op v
constExpr f (EIf r1 r2 r3)    = do
  v <- constExpr f r1
  b <- maybeT (valToBool v)
  if b then constExpr f r2 else constExpr f r3
constExpr f (ECast τvl r)     = do
  τ <- constExpr f τvl
  v <- constExpr f r
  cast v τ
constExpr _ (ELVal a)         = return a
constExpr f (EVar x)          = f x >>= blockPointer
constExpr f (EDeref r)        = do
  VBase _ (VPointer p) <- constExpr f r
  guard (pInRange p)
  return p
constExpr f (ELField su i l)  = do
  p <- constExpr f l
  pBranch su i p
constExpr _ _                 = nothingT

constExpr_ :: Expr a -> Maybe a
constExpr_ e = evalState (runMaybeT (constExpr (\_ -> nothingT) e)) emptyMem

vlErase :: VLType -> Type
vlErase (VLType τ)      = τ
vlErase (VLPointer c τ) = TBase c (TPointer (vlErase τ))
vlErase (VLArray τ r)   = case constExpr_ r of
  Just (VBase _ (VInt n)) -> TArray (vlErase τ) (fromEnum n)
  _                       -> TArray (vlErase τ) 0

{- Expression contexts -}
data ECtx :: * -> * -> * where
  CtxTop     :: ECtx b b
  -- for types
  CtxPointer :: Bool -> TCtx b -> TCtx b
  CtxArrayL  :: RExpr -> TCtx b -> TCtx b
  CtxCastL   :: RExpr -> RCtx b -> TCtx b
  -- for right expressions
  CtxCall    :: Id -> [RExpr] -> [RExpr] -> RCtx b -> RCtx b
  CtxAssignR :: LExpr -> RCtx b -> RCtx b
  CtxField   :: StructUnion -> Int -> RCtx b -> RCtx b
  CtxBinOpL  :: BinOp -> RExpr -> RCtx b -> RCtx b
  CtxBinOpR  :: BinOp -> RExpr -> RCtx b -> RCtx b
  CtxUnOp    :: UnOp -> RCtx b -> RCtx b
  CtxPreOpR  :: BinOp -> LExpr -> RCtx b -> RCtx b
  CtxPostOpR :: BinOp -> LExpr -> RCtx b -> RCtx b
  CtxCastR   :: VLType -> RCtx b -> RCtx b
  CtxArrayR  :: VLType -> TCtx b -> RCtx b
  CtxDeref   :: LCtx b -> RCtx b
  CtxIf      :: RExpr -> RExpr -> RCtx b -> RCtx b
  CtxComma   :: RExpr -> RCtx b -> RCtx b
  -- for left expressions
  CtxToVal   :: RCtx b -> LCtx b
  CtxAssignL :: RExpr -> RCtx b -> LCtx b
  CtxLField  :: StructUnion -> Int -> LCtx b -> LCtx b
  CtxAddrOf  :: RCtx b -> LCtx b
  CtxPreOpL  :: BinOp -> RExpr -> RCtx b -> LCtx b
  CtxPostOpL :: BinOp -> RExpr -> RCtx b -> LCtx b

type TCtx = ECtx Type
type RCtx = ECtx RVal
type LCtx = ECtx LVal

deriving instance Eq (ECtx a b)
deriving instance Show (ECtx a b)

eCtxMap :: (VLType -> VLType) -> (RExpr -> RExpr) -> (LExpr -> LExpr) -> ECtx a b -> ECtx a b
eCtxMap ft fr fl = m
 where
  m :: ECtx a b -> ECtx a b
  m CtxTop                = CtxTop
  m (CtxPointer c k)      = CtxPointer c (m k)
  m (CtxArrayL r k)       = CtxArrayL (fr r) (m k)
  m (CtxCastL r k)        = CtxCastL (fr r) (m k)
  m (CtxCall x rsl rsr k) = CtxCall x (fr <$> rsl) (fr <$> rsr) (m k)
  m (CtxAssignR l k)      = CtxAssignR (fl l) (m k)
  m (CtxField su i k)     = CtxField su i (m k)
  m (CtxBinOpL op r2 k)   = CtxBinOpL op (fr r2) (m k)
  m (CtxBinOpR op r1 k)   = CtxBinOpR op (fr r1) (m k)
  m (CtxUnOp op k)        = CtxUnOp op (m k)
  m (CtxPreOpR op l k)    = CtxPreOpR op (fl l) (m k)
  m (CtxPostOpR op l k)   = CtxPostOpR op (fl l) (m k)
  m (CtxCastR τ k)        = CtxCastR (ft τ) (m k)
  m (CtxArrayR τ k)       = CtxArrayR (ft τ) (m k)
  m (CtxDeref k)          = CtxDeref (m k)
  m (CtxIf rt rf k)       = CtxIf (fr rt) (fr rf) (m k)
  m (CtxComma r2 k)       = CtxComma (fr r2) (m k)
  m (CtxToVal k)          = CtxToVal (m k)
  m (CtxAssignL r k)      = CtxAssignL (fr r) (m k)
  m (CtxLField su i k)    = CtxLField su i (m k)
  m (CtxAddrOf k)         = CtxAddrOf (m k)
  m (CtxPreOpL op r k)    = CtxPreOpL op (fr r) (m k)
  m (CtxPostOpL op r k)   = CtxPostOpL op (fr r) (m k)

class Subst a b c | a b -> c where
  subst :: a -> b -> c

instance Subst (ECtx a b) (Expr a) (Expr b) where
  subst CtxTop                b  = b
  subst (CtxPointer c k)      τ  = subst k (VLPointer c τ)
  subst (CtxArrayL r k)       τ  = subst k (VLArray τ r)
  subst (CtxCastL r k)        τ  = subst k (ECast τ r)
  subst (CtxCall x rsl rsr k) r  = subst k (ECall x (reverse rsl ++ [r] ++ rsr))
  subst (CtxAssignR l k)      r  = subst k (EAssign l r)
  subst (CtxField su i k)     r  = subst k (EField su i r)
  subst (CtxBinOpL op r2 k)   r1 = subst k (EBinOp op r1 r2)
  subst (CtxBinOpR op r1 k)   r2 = subst k (EBinOp op r1 r2)
  subst (CtxUnOp op k)        r  = subst k (EUnOp op r)
  subst (CtxPreOpR op l k)    r  = subst k (EPreOp op l r)
  subst (CtxPostOpR op l k)   r  = subst k (EPostOp op l r)
  subst (CtxCastR τ k)        r  = subst k (ECast τ r)
  subst (CtxArrayR τ k)       r  = subst k (VLArray τ r)
  subst (CtxDeref k)          r  = subst k (EDeref r)
  subst (CtxIf rt rf k)       r  = subst k (EIf r rt rf)
  subst (CtxComma r2 k)       r1 = subst k (EComma r1 r2)
  subst (CtxToVal k)          l  = subst k (EToVal l)
  subst (CtxAssignL r k)      l  = subst k (EAssign l r)
  subst (CtxLField su i k)    l  = subst k (ELField su i l)
  subst (CtxAddrOf k)         l  = subst k (EAddrOf l)
  subst (CtxPreOpL op r k)    l  = subst k (EPreOp op l r)
  subst (CtxPostOpL op r k)   l  = subst k (EPostOp op l r)

data Redex b where
  RedPointer  :: TCtx b -> Type -> Redex b
  RedArray    :: TCtx b -> Type -> RVal -> Redex b
  RedCall     :: RCtx b -> Id -> [RVal] -> Redex b
  RedAssign   :: RCtx b -> LVal -> RVal -> Redex b
  RedToVal    :: RCtx b -> LVal -> Redex b
  RedAddrOf   :: RCtx b -> LVal -> Redex b
  RedFieldCis :: RCtx b -> Int -> Int -> RVal -> Redex b
  RedField    :: RCtx b -> StructUnion -> Int -> RVal -> Redex b
  RedBinOp    :: RCtx b -> BinOp -> RVal -> RVal -> Redex b
  RedUnOp     :: RCtx b -> UnOp -> RVal -> Redex b
  RedPreOp    :: RCtx b -> BinOp -> LVal -> RVal -> Redex b
  RedPostOp   :: RCtx b -> BinOp -> LVal -> RVal -> Redex b
  RedCast     :: RCtx b -> Type -> RVal -> Redex b
  RedIf       :: RCtx b -> RVal -> RExpr -> RExpr -> Redex b
  RedComma    :: RCtx b -> RVal -> RExpr -> Redex b
  RedVar      :: LCtx b -> Id -> Redex b
  RedDeref    :: LCtx b -> RVal -> Redex b
  RedLField   :: LCtx b -> StructUnion -> Int -> LVal -> Redex b

instance Eq (Redex b) where
  r1 == r2 = case (r1,r2) of _ -> r1 == r2
instance Show (Redex b) where
  show r = case r of _ -> show r

{- Splitting expressions -}
split :: Expr a -> Either a [Redex a]
split = split' CtxTop
 where
  split' :: ECtx a b -> Expr a -> Either a [Redex b]
  split' _ (VLType τ)        = Left τ
  split' k (VLPointer c τ)   = case split' (CtxPointer c k) τ of
    Left σ    -> Right [RedPointer k σ]
    Right rds -> Right rds
  split' k (VLArray τ r)     = case (split' (CtxArrayL r k) τ, split' (CtxArrayR τ k) r) of
    (Left σ,     Left v)     -> Right [RedArray k σ v]
    (Right rds,  Left _)     -> Right rds
    (Left _,     Right rds)  -> Right rds
    (Right rds1, Right rds2) -> Right (rds1 ++ rds2)
  split' _ (EVal v)          = Left v
  split' k (ECall x rs)      = case splitArgs [] rs of
    Left vs   -> Right [RedCall k x vs]
    Right rds -> Right rds
   where
    splitArgs _   []      = Left []
    splitArgs rsr (r:rsl) = case (split' (CtxCall x rsr rsl k) r, splitArgs (r:rsr) rsl) of
      (Left v,    Left vs)     -> Left (v:vs)
      (Right rds, Left _)      -> Right rds
      (Left _,    Right rds)   -> Right rds
      (Right rds1, Right rds2) -> Right (rds1 ++ rds2)
  split' k (EAssign l r)     = case (split' (CtxAssignL r k) l, split' (CtxAssignR l k) r) of
    (Left lv,    Left v)     -> Right [RedAssign k lv v]
    (Right rds,  Left _)     -> Right rds
    (Left _,     Right rds)  -> Right rds
    (Right rds1, Right rds2) -> Right (rds1 ++ rds2)
  split' k (EToVal l)        = case split' (CtxToVal k) l of
    Left lv   -> Right [RedToVal k lv]
    Right rds -> Right rds
  split' k (EAddrOf l)       = case split' (CtxAddrOf k) l of
    Left lv   -> Right [RedAddrOf k lv]
    Right rds -> Right rds
  split' k (EField Struct i (EField Union j r))
                             = case split' (CtxField Union j (CtxField Struct i k)) r of
    Left v    -> Right [RedFieldCis k i j v]
    Right rds -> Right rds
  split' k (EField su i r)   = case split' (CtxField su i k) r of
    Left v    -> Right [RedField k su i v]
    Right rds -> Right rds
  split' k (EBinOp op r1 r2) = case (split' (CtxBinOpL op r2 k) r1, split' (CtxBinOpR op r1 k) r2) of
    (Left v1,    Left v2)    -> Right [RedBinOp k op v1 v2]
    (Right rds,  Left _)     -> Right rds
    (Left _,     Right rds)  -> Right rds
    (Right rds1, Right rds2) -> Right (rds1 ++ rds2)
  split' k (EUnOp op r)      = case split' (CtxUnOp op k) r of
    Left v    -> Right [RedUnOp k op v]
    Right rds -> Right rds
  split' k (EPreOp op l r)   = case (split' (CtxPreOpL op r k) l, split' (CtxPreOpR op l k) r) of
    (Left lv,    Left v)     -> Right [RedPreOp k op lv v]
    (Right rds,  Left _)     -> Right rds
    (Left _,     Right rds)  -> Right rds
    (Right rds1, Right rds2) -> Right (rds1 ++ rds2)
  split' k (EPostOp op l r)  = case (split' (CtxPostOpL op r k) l, split' (CtxPostOpR op l k) r) of
    (Left lv,    Left v)     -> Right [RedPostOp k op lv v]
    (Right rds,  Left _)     -> Right rds
    (Left _,     Right rds)  -> Right rds
    (Right rds1, Right rds2) -> Right (rds1 ++ rds2)
  split' k (ECast τ r)       = case (split' (CtxCastL r k) τ, split' (CtxCastR τ k) r) of
    (Left σ,     Left v)     -> Right [RedCast k σ v]
    (Right rds,  Left _)     -> Right rds
    (Left _,     Right rds)  -> Right rds
    (Right rds1, Right rds2) -> Right (rds1 ++ rds2)
  split' k (EIf r rt rf)     = case split' (CtxIf rt rf k) r of
    Left v    -> Right [RedIf k v rt rf]
    Right rds -> Right rds
  split' k (EComma r1 r2)    = case split' (CtxComma r2 k) r1 of
    Left v    -> Right [RedComma k v r2]
    Right rds -> Right rds
  split' _ (ELVal lv)        = Left lv
  split' k (EVar x)          = Right [RedVar k x]
  split' k (EDeref r)        = case split' (CtxDeref k) r of
    Left v    -> Right [RedDeref k v]
    Right rds -> Right rds
  split' k (ELField su i l)  = case split' (CtxLField su i k) l of
    Left lv   -> Right [RedLField k su i lv]
    Right rds -> Right rds

