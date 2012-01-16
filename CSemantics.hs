{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XTypeSynonymInstances #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XFunctionalDependencies #-}
{-# OPTIONS -XUndecidableInstances #-}
{-# OPTIONS -XFlexibleContexts #-}
{-# OPTIONS -XGADTs #-}
{-# OPTIONS -XKindSignatures #-}
{-# OPTIONS -XRankNTypes #-}
{-# OPTIONS -XStandaloneDeriving #-}
{-# OPTIONS -XTupleSections #-}

module CSemantics where

import Util
import Types
import Values
import SimpleMemory
import Pointers
import Memory
import RLValues
import Expressions
import Statements

import Prelude
import Control.Monad
import Control.Applicative

data Fun = Fun {
  funArgs :: Assoc Id Type,
  funType :: Type,
  funStmt :: Stmt
} deriving (Eq, Show, Ord)

instantiate :: (MonadPlus m, MemWriter m) => Fun -> [RVal] -> m SInCtx
instantiate (Fun xs _ s) vs = do
  guard (length xs == length vs)
  guardM (allM isDeterminate vs)
  ads <- assocMapM f (zipWith (\(x,_) rv -> (x,rv)) xs vs)
  return ([CtxBlock ads], s)
 where
  f :: (MonadPlus m, MemWriter m) => RVal -> m AllocDecl
  f v = AllocAuto <$> alloc (typeOf v) (Just (aVal v)) MAuto

data Return = forall b . Return (EInSCtx b) (RCtx b)

instance Eq Return where
  Return es1 k1 == Return es2 k2 = case (eInS es1, eInS es2) of
    (CtxVLDeclT _ _,  CtxVLDeclT _ _) -> es1 == es2 && k1 == k2
    (CtxExpr,         CtxExpr)        -> es1 == es2 && k1 == k2
    (CtxReturn,       CtxReturn)      -> es1 == es2 && k1 == k2
    (CtxIfE _ _,      CtxIfE _ _)     -> es1 == es2 && k1 == k2
    (CtxSwitchE _,    CtxSwitchE _)   -> es1 == es2 && k1 == k2
    _                                 -> False

instance Ord Return where
  Return es1 k1 <= Return es2 k2 = case (eInS es1, eInS es2) of
    (CtxVLDeclT _ _,  CtxVLDeclT _ _) -> if es1 /= es2 then es1 <= es2 else k1 <= k2
    (CtxExpr,         CtxExpr)        -> True
    (CtxExpr,         CtxReturn)      -> True
    (CtxExpr,         CtxIfE _ _)     -> True
    (CtxExpr,         CtxSwitchE _)   -> True
    (CtxReturn,       CtxReturn)      -> True
    (CtxReturn,       CtxIfE _ _)     -> True
    (CtxReturn,       CtxSwitchE _)   -> True
    (CtxIfE _ _,      CtxIfE _ _)     -> if es1 /= es2 then es1 <= es2 else k1 <= k2
    (CtxIfE _ _,      CtxSwitchE _)   -> True
    (CtxSwitchE _,    CtxSwitchE _)   -> if es1 /= es2 then es1 <= es2 else k1 <= k2
    _                                 -> False

{- Evaluation -}
class (MonadPlus m, MemWriter m) => CMonad m where
  getFun         :: Id -> m Fun
  getGlobal      :: Id -> m Block
  sequencedLoad  :: LVal -> m RVal
  sequencedStore :: LVal -> RVal -> m ()
  sequencePoint  :: m ()
  pushReturn     :: Return -> m ()
  popReturn      :: m (Maybe Return)
  pickRedex      :: [Redex a] -> m (Redex a)

getVar :: CMonad m => Id -> SCtx -> m Block
getVar x ek = maybeZero (getLocal x ek) `mplus` getGlobal x

varLVal :: CMonad m => Id -> SCtx -> m LVal
varLVal x k = getVar x k >>= blockPointer

typeOfGlobal :: CMonad m => Id -> m Type
typeOfGlobal x = getGlobal x >>= typeOfBlock

{- Evaluation -}
data E =
  ES SInCtx | -- evaluating a statement
  forall b . EE (EInSCtx b) (Expr b) | -- evaluating an expression
  forall b . EV (EInSCtx b) (RCtx b) | -- evaluating void
  EF RVal -- and ... we're done!

instance Show E where
  show (ES sk)   = show sk
  show (EE es b) = show (subst (eInS es) b)
  show (EV es k) = show es ++ show k
  show (EF mv)   = show mv

nextExpr :: CMonad m => EInSCtx b -> ECtx a b -> Expr a -> m E
nextExpr es k a = return (EE es (subst k a))

nextExprA :: CMonad m => EInSCtx b -> RCtx b -> RAVal -> m E
nextExprA es k ar = do
  pv <- aToVal ar
  case pv of
    Left p  -> nextExpr es' k (EVal (VBase False (VPointer p)))
     where es' = es { eTmps = blockOf p:eTmps es }
    Right v -> nextExpr es k (EVal v)

funReturn :: CMonad m => Maybe RVal -> SInCtx -> m E
funReturn (Just v) sk = do
  _ <- toTop sk -- free all declarations
  mr <- popReturn
  guardM (isDeterminate v)
  case mr of
    Nothing            -> return (EF v)
    Just (Return es k) -> nextExpr es k (EVal v)
funReturn Nothing sk = do
  _ <- toTop sk -- free all declarations
  mr <- popReturn
  case mr of
    Nothing            -> return (EF (VBase False (VInt 0)))
    Just (Return es k) -> return (EV es k)

nextStmt :: CMonad m => SInCtx -> m E
nextStmt sk = next sk >>= maybe (funReturn Nothing sk) (return . ES)

valStep :: CMonad m => EInSCtx b -> b -> m E
valStep (EInSCtx k es ae tmps) a = do
  sequencePoint
  _ <- mapM (free False) tmps -- free all objects with temporary storage
  case es of
    CtxVLDeclT x s -> do
      b <- alloc a Nothing MAuto
      return (ES (CtxVLDecl x ae b:k, s))
    CtxExpr        -> do
      guardM (isDeterminate a)
      nextStmt (k, SExpr ae)
    CtxReturn      -> do
      guardM (isDeterminate a)
      funReturn (Just a) (k, SReturn (Just ae)) -- a could have been freed
    CtxIfE st sf   -> do
      guardM (isDeterminate a)
      b <- maybeZero (valToBool a) -- a could have been freed
      if b
      then return (ES (CtxIfT ae sf:k, st))
      else return (ES (CtxIfF ae st:k, sf))
    CtxSwitchE s   -> case a of
      VBase _ (VInt n) -> ES <$> toCase n (CtxSwitch ae:k, s)
      _                -> mzero

{- Evaluation of statements -}
stmtStep :: CMonad m => SInCtx -> m E
stmtStep (k, SBlock ds s)        = do
  ads <- assocMapM allocD ds
  return (ES (CtxBlock ads:k, s))
stmtStep (k, SVLDecl x τ s)      = return (EE (ctxVLDeclT k x τ s) τ)
stmtStep (k, SExpr r)            = return (EE (ctxExpr k r) r)
stmtStep (k, SIf r st sf)        = return (EE (ctxIfE k r st sf) r)
stmtStep (k, SSwitch r s)        = return (EE (ctxSwitchE k r s) r)
stmtStep sk@(_, SGoto l)         = ES <$> toLabel l sk
stmtStep (k, SLabel l s)         = return (ES (CtxLabel l:k, s))
stmtStep (k, SCase c s)          = return (ES (CtxCase c:k, s))
stmtStep (k, SLoop s)            = return (ES (CtxLoop:k, s))
stmtStep sk@(_, STrap t)         = toTrap t sk >>= nextStmt
stmtStep (k, SSetTrap t s)       = return (ES (CtxSetTrap t:k, s))
stmtStep (k, SReturn (Just r))   = return (EE (ctxReturn k r) r)
stmtStep sk@(_, SReturn Nothing) = funReturn Nothing sk
stmtStep (k, SComp sl sr)        = return (ES (CtxCompL sr:k, sl))
stmtStep sk@(_, SSkip)           = nextStmt sk

{- Evaluation of expressions -}
redexStep :: CMonad m => EInSCtx b -> Redex b -> m E
redexStep es (RedPointer k τ)               = nextExpr es k (VLType (TBase False (TPointer τ)))
redexStep es (RedArray k τ v)               = case v of
  VBase _ (VInt n) | n >= 1 -> nextExpr es k (VLType (TArray τ (fromEnum n)))
  _                         -> mzero
redexStep es (RedCall k x vs)               = do
  sequencePoint
  f <- getFun x
  pushReturn (Return es k)
  ES <$> instantiate f vs
redexStep es (RedAssign k p v)              = do
  sequencedStore p v -- fails if a is indeterminate
  nextExpr es k (EVal v)
redexStep es (RedToVal k p)                 = case typeOf p of
   TArray τ _ -> do
     guardM (isDeterminate p)
     let p' = p { pType = τ } in nextExpr es k (EVal (VBase False (VPointer p')))
   _          -> sequencedLoad p >>= nextExpr es k . EVal . remConst -- fails if a is indeterminate
redexStep es (RedAddrOf k p)                = do
  guardM (isDeterminate p)
  nextExpr es k (EVal (VBase False (VPointer p)))
redexStep es (RedFieldCis k i j' v)         = case v of
  VUnion _ u (Just (j,VArray _ [VStruct _ _ vs])) -> do
    ci <- cisFields u j j'
    guard (i <= ci)
    maybeZero (vs !? i) >>= nextExprA es k
  _                                               -> mzero
redexStep es (RedField k Struct i v)        = case v of
  VStruct _ _ vs -> maybeZero (vs !? i) >>= nextExprA es k
  _              -> mzero
redexStep es (RedField k Union j v)         = case v of
  VUnion _ _ (Just (j',v')) | j' == j -> nextExprA es k v'
  _                                   -> mzero
redexStep es (RedBinOp k op v1 v2)          = do
  guardM (isDeterminate v1)
  guardM (isDeterminate v2)
  evalBinOp op v1 v2 >>= nextExpr es k . EVal
redexStep es (RedUnOp k op v)               = evalUnOp op v >>= nextExpr es k . EVal
redexStep es (RedPreOp k op p v2)           = do
  v1 <- sequencedLoad p -- fails if a is indeterminate
  guardM (isDeterminate v2)
  v <- evalBinOp op v1 v2
  sequencedStore p v
  nextExpr es k (EVal v)
redexStep es (RedPostOp k op p v2)          = do
  v1 <- sequencedLoad p -- fails if a is indeterminate
  guardM (isDeterminate v2)
  v <- evalBinOp op v1 v2
  sequencedStore p v
  nextExpr es k (EVal v1)
redexStep es (RedCast k τ v)                = do
  guardM (isDeterminate v)
  v' <- cast v τ
  nextExpr es k (EVal v')
redexStep es (RedIf k v r1 r2)              = do
  guardM (isDeterminate v)
  b <- maybeZero (valToBool v)
  nextExpr es k (if b then r1 else r2)
redexStep es (RedComma k _ r)               = do
  sequencePoint
  return (EE es (subst k r))
redexStep es (RedVar k x)                   = varLVal x (eCtx es) >>= nextExpr es k . ELVal
redexStep es (RedDeref k v)                 = case v of
  VBase _ (VPointer p) -> do
    guardM (isDeterminate p)
    guard (pInRange p)
    nextExpr es k (ELVal p)
  _                    -> mzero
redexStep es (RedLField k su i p)           = do
  p' <- pBranch su i p -- fails if a is indeterminate
  nextExpr es k (ELVal p')

{- Evaluation of void -}
voidStep :: CMonad m => EInSCtx b -> RCtx b -> m E
voidStep (EInSCtx k CtxExpr ae tmps) CtxTop         = do
  _ <- mapM (free False) tmps
  nextStmt (k, SExpr ae)
voidStep es                          (CtxComma r k) = nextExpr es k r
voidStep _                           _              = mzero

{- Glueing it all together -}
hasSideEffects :: Redex b -> Bool
hasSideEffects (RedCall _ _ _)     = True 
hasSideEffects (RedAssign _ _ _)   = True
hasSideEffects (RedToVal _ _)      = True
hasSideEffects (RedPreOp _ _ _ _)  = True
hasSideEffects (RedPostOp _ _ _ _) = True
hasSideEffects _                   = False

step :: CMonad m => E -> m E
step (ES sk)   = stmtStep sk
step (EE es e) = case split e of
  Left b    -> valStep es b
  Right rds -> pickRedex rds >>= redexStep es
step (EV es k) = voidStep es k
step (EF _)    = mzero

eval :: CMonad m => E -> m RVal
eval (EF v) = return v
eval e      = {- trace (show e ++ "\n") $ -} step e >>= eval

evalStmt :: CMonad m => Stmt -> m RVal
evalStmt s = eval (ES ([], s))

evalFun :: CMonad m => Id -> m RVal
evalFun x = do
  Fun _ _ s <- getFun x
  evalStmt s

