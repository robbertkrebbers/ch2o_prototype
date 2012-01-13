{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XTypeSynonymInstances #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XFunctionalDependencies #-}
{-# OPTIONS -XUndecidableInstances #-}
{-# OPTIONS -XFlexibleContexts #-}
{-# OPTIONS -XIncoherentInstances #-}
{-# OPTIONS -XGADTs #-}
{-# OPTIONS -XKindSignatures #-}
{-# OPTIONS -XRankNTypes #-}
{-# OPTIONS -XStandaloneDeriving #-}

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
import Control.Monad.State
import Control.Monad.Maybe
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map

data Fun = Fun {
  funArgs :: Assoc Id Type,
  funType :: Type,
  funStmt :: Stmt
} deriving (Eq, Show)

data Return = forall b . Return (EInSCtx b) (RCtx b)

{- States -}
data CState = CState {
  stateMem     :: Mem,
  stateFuns    :: Map Id Fun,
  stateGlobals :: Map Id Block,
  stateReturns :: [Return]
}

type CMonad = State CState
type CMaybe = MaybeT CMonad

runCMaybe :: CMaybe a -> CState -> (Maybe a, CState)
runCMaybe m s = runState (runMaybeT m) s

instance EnvReader CMonad where
  getEnv = gets (mEnv . stateMem)
instance SimpleMemReader MBVal CMonad where
  getMem = gets stateMem
instance SimpleMemWriter MBVal CMonad where
  setMem m = modify $ \s -> s { stateMem = m }

getGlobal :: Id -> CMaybe Block
getGlobal x = gets stateGlobals >>= maybeT . Map.lookup x

getVar :: Id -> SCtx -> CMaybe Block
getVar x ek = maybeT (getLocal x ek) `mplus` getGlobal x

varLVal :: Id -> SCtx -> CMaybe LVal
varLVal x k = getVar x k >>= blockPointer

typeOfGlobal :: Id -> CMaybe Type
typeOfGlobal x = getGlobal x >>= typeOfBlock

getFun :: Id -> CMaybe Fun
getFun x = gets stateFuns >>= maybeT . Map.lookup x

pushReturn :: Return -> CMonad ()
pushReturn r = modify $ \s -> s { stateReturns = r:stateReturns s }

popReturn :: CMonad (Maybe Return)
popReturn = do
  rs <- gets stateReturns
  case rs of
    []      -> return Nothing
    (r:rs') -> do modify $ \s -> s { stateReturns = rs' }; return (Just r)

instantiate :: MemWriter m => Fun -> [RVal] -> MaybeT m SInCtx
instantiate (Fun xs _ s) vs = do
  guard (length xs == length vs)
  guardM (allM isDeterminate vs)
  ads <- assocMapM f (zipWith (\(x,_) rv -> (x,rv)) xs vs)
  return ([CtxBlock ads], s)
 where
  f :: MemWriter m => RVal -> MaybeT m AllocDecl
  f v = AllocAuto <$> alloc (typeOf v) (Just (aVal v)) MAuto

{- Evaluation -}
data E =
  ES SInCtx | -- evaluating a statement
  forall b . EE (EInSCtx b) (Expr b) | -- evaluating an expression
  EF (Maybe RVal) -- and ... we're done!

instance Show E where
  show (ES sk)   = show sk
  show (EE es b) = show (subst (eInS es) b)
  show (EF mv)   = show mv

nextExpr :: EInSCtx b -> ECtx a b -> Expr a -> CMaybe E
nextExpr es k a = return (EE es (subst k a))

nextExprA :: EInSCtx b -> RCtx b -> RAVal -> CMaybe E
nextExprA es k ar = do
  (mb,v) <- aToVal ar
  case mb of
    Nothing -> nextExpr es k (EVal v)
    Just b  -> nextExpr (es { eTmps = b:eTmps es }) k (EVal v)

valStep :: EInSCtx b -> b -> CMaybe E
valStep (EInSCtx k es ae tmps) a = do
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
      b <- maybeT (valToBool a) -- a could have been freed
      if b
      then return (ES (CtxIfT ae sf:k, st))
      else return (ES (CtxIfF ae st:k, sf))
    CtxSwitchE s   -> case a of
      VBase _ (VInt n) -> ES <$> toCase n (CtxSwitch ae:k, s)
      _                -> nothingT

funReturn :: Maybe RVal -> SInCtx -> CMaybe E
funReturn (Just v) sk = do
  _ <- toTop sk -- free all declarations
  mr <- lift popReturn
  case mr of
    Nothing            -> return (EF (Just v))
    Just (Return es k) -> nextExpr es k (EVal v)
funReturn Nothing sk = do
  _ <- toTop sk -- free all declarations
  mr <- lift popReturn
  case mr of
    Nothing                                          -> return (EF Nothing)
    Just (Return (EInSCtx k CtxExpr ae tmps) CtxTop) -> do
      _ <- mapM (free False) tmps
      nextStmt (k, SExpr ae)
    Just (Return es (CtxComma r k))                  -> nextExpr es k r
    Just _                                           -> nothingT

nextStmt :: SInCtx -> CMaybe E
nextStmt sk = next sk >>= maybe (funReturn Nothing sk) (return . ES)

{- Evaluation of statements -}
stmtStep :: SInCtx -> CMaybe E
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
redexStep :: EInSCtx b -> Redex b -> CMaybe E
redexStep es (RedPointer k τ)               = nextExpr es k (VLType (TBase False (TPointer τ)))
redexStep es (RedArray k τ v)               = case v of
  VBase _ (VInt n) | n >= 1 -> nextExpr es k (VLType (TArray τ (fromEnum n)))
  _                         -> nothingT
redexStep es (RedCall k x vs)               = do
  f <- getFun x
  lift (pushReturn (Return es k))
  ES <$> instantiate f vs
redexStep es (RedAssign k p v)              = do
  store p v -- fails if a is indeterminate
  nextExpr es k (EVal v)
redexStep es (RedToVal k p)                 = case typeOf p of
   TArray τ _ -> do
     guardM (isDeterminate p)
     let p' = p { pType = τ } in nextExpr es k (EVal (VBase False (VPointer p')))
   _          -> load p >>= nextExpr es k . EVal . remConst -- fails if a is indeterminate
redexStep es (RedAddrOf k p)                = do
  guardM (isDeterminate p)
  nextExpr es k (EVal (VBase False (VPointer p)))
redexStep es (RedFieldCis k i j' v)         = case v of
  VUnion _ u (Just (j,VArray _ [VStruct _ _ vs])) -> do
    ci <- cisFields u j j'
    guard (i <= ci)
    maybeT (vs !? i) >>= nextExprA es k
  _                                               -> nothingT
redexStep es (RedField k Struct i v)        = case v of
  VStruct _ _ vs -> maybeT (vs !? i) >>= nextExprA es k
  _              -> nothingT
redexStep es (RedField k Union j v)         = case v of
  VUnion _ _ (Just (j',v')) | j' == j -> nextExprA es k v'
  _                                   -> nothingT
redexStep es (RedBinOp k op v1 v2)          = do
  guardM (isDeterminate v1)
  guardM (isDeterminate v2)
  evalBinOp op v1 v2 >>= nextExpr es k . EVal
redexStep es (RedUnOp k op v)               = evalUnOp op v >>= nextExpr es k . EVal
redexStep es (RedPreOp k op p v2)           = do
  v1 <- load p -- fails if a is indeterminate
  guardM (isDeterminate v2)
  v <- evalBinOp op v1 v2
  store p v
  nextExpr es k (EVal v)
redexStep es (RedPostOp k op p v2)          = do
  v1 <- load p -- fails if a is indeterminate
  guardM (isDeterminate v2)
  v <- evalBinOp op v1 v2
  store p v
  nextExpr es k (EVal v1)
redexStep es (RedCast k τ v)                = do
  guardM (isDeterminate v)
  v' <- cast v τ
  nextExpr es k (EVal v')
redexStep es (RedIf k v r1 r2)              = do
  guardM (isDeterminate v)
  b <- maybeT (valToBool v)
  nextExpr es k (if b then r1 else r2)
redexStep es (RedComma k _ r)               = do
  return (EE es (subst k r))
redexStep es (RedVar k x)                   = varLVal x (eCtx es) >>= nextExpr es k . ELVal
redexStep es (RedDeref k v)                 = case v of
  VBase _ (VPointer p) -> do
    guardM (isDeterminate p)
    guard (pInRange p)
    nextExpr es k (ELVal p)
  _                    -> nothingT
redexStep es (RedLField k su i p)           = do
  p' <- pBranch su i p -- fails if a is indeterminate
  nextExpr es k (ELVal p')

{- Glueing it all together -}
step :: E -> CMaybe E
step (ES sk)   = stmtStep sk
step (EE es e) = case split e of
  Left b    -> valStep es b
  Right rds -> redexStep es (head rds) -- Just pick the first ;)
step (EF _)    = nothingT

eval :: E -> CMaybe (Maybe RVal)
eval (EF mv) = return mv
eval e       = {- trace (show e ++ "\n") $ -} step e >>= eval

evalStmt :: Stmt -> CMaybe (Maybe RVal)
evalStmt s = eval (ES ([], s))

evalFun :: Id -> CMaybe (Maybe RVal)
evalFun x = do
  Fun _ _ s <- getFun x
  evalStmt s

