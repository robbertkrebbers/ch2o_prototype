{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XGADTs #-}
{-# OPTIONS -XKindSignatures #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XUndecidableInstances #-}
{-# OPTIONS -XFlexibleContexts #-}
{-# OPTIONS -XStandaloneDeriving #-}
{-# OPTIONS -XFunctionalDependencies #-}

module Statements where

import Util
import Types
import SimpleMemory
import RLValues
import Memory
import Expressions

import Prelude
import Control.Monad
import Control.Applicative

{- Declarations -}
data Decl = DAuto Type | DStatic Block deriving (Eq, Show, Ord)
data AllocDecl = AllocAuto Block | AllocStatic Block deriving (Eq, Show, Ord)

allocD :: (MonadPlus m, MemWriter m) => Decl -> m AllocDecl
allocD (DAuto τ)   = alloc τ Nothing MAuto >>= return . AllocAuto
allocD (DStatic b) = return (AllocStatic b)

freeD :: (MonadPlus m, MemWriter m) => AllocDecl -> m Decl
freeD (AllocAuto b)   = do
  τ <- typeOfBlock b
  free False b
  return (DAuto τ)
freeD (AllocStatic b) = return (DStatic b)

instance BlockOf AllocDecl where
  blockOf (AllocAuto b)   = b
  blockOf (AllocStatic b) = b

{- Statements -}
data Trap = Continue | Break deriving (Eq, Show, Ord)

data Stmt =
  SExpr RExpr |
  SReturn (Maybe RExpr) |
  SBlock (Assoc Id Decl) Stmt |
  SVLDecl Id VLType Stmt |
  SSkip |
  SComp Stmt Stmt |
  SIf RExpr Stmt Stmt |
  SSwitch RExpr Stmt | -- does not catch breaks, use sSwitch instead
  SGoto Id |
  SLabel Id Stmt |
  SCase (Maybe Integer) Stmt | -- Nothing represents default:
  SLoop Stmt |
  STrap Trap |
  SSetTrap Trap Stmt
  deriving (Eq, Show, Ord)

sContinue :: Stmt
sContinue = STrap Continue

sBreak :: Stmt
sBreak = STrap Break

sSwitch :: RExpr -> Stmt -> Stmt
sSwitch e s = SSetTrap Break (SSwitch e s)

{- while (e) s -}
sWhile :: RExpr -> Stmt -> Stmt
sWhile e s = SSetTrap Break (SLoop loopbody)
 where
  loopbody = SIf e (SSetTrap Continue s) sBreak

{- do s while (e) -}
sDoWhile :: Stmt -> RExpr -> Stmt
sDoWhile s e = SSetTrap Break (SLoop loopbody)
 where
  loopbody = SComp (SSetTrap Continue s) (SIf e SSkip sBreak)

{- for (; me2; me3) s -}
sFor :: Maybe RExpr -> Maybe RExpr -> Stmt -> Stmt
sFor me2 me3 s = SSetTrap Break (SLoop loopbody)
 where
  loopbody = case me2 of
    Nothing -> innerbody
    Just e2 -> SIf e2 innerbody sBreak
  innerbody = case me3 of
    Nothing -> SSetTrap Continue s
    Just e3 -> SComp (SSetTrap Continue s) (SExpr e3)

{- s1; s2; ...; s3 -}
sComps :: [Stmt] -> Stmt
sComps = foldr SComp SSkip

{- Statement contexts -}
data SCtxSeg =
  CtxBlock (Assoc Id AllocDecl) |
  CtxVLDecl Id VLType Block |
  CtxCompL Stmt |
  CtxCompR Stmt |
  CtxIfT RExpr Stmt |
  CtxIfF RExpr Stmt |
  CtxSwitch RExpr |
  CtxLabel Id |
  CtxCase (Maybe Integer) |
  CtxLoop |
  CtxSetTrap Trap
  deriving (Eq, Show, Ord)

type SCtx = [SCtxSeg]
type SInCtx = (SCtx,Stmt)

getLocal :: Id -> SCtx -> Maybe Block
getLocal _ []                   = Nothing
getLocal x (CtxBlock ds:k)      = (blockOf <$> lookup x ds) `mplus` getLocal x k
getLocal x (CtxVLDecl x' _ b:k) = if x == x' then Just b else getLocal x k
getLocal x (_:k)                = getLocal x k

data PathSeg = Up | Down Int deriving (Eq, Show, Ord)
type Path = [PathSeg]

changeCtx :: (MonadPlus m, MemWriter m) => Path -> SInCtx -> m SInCtx
changeCtx [] sc                         = return sc
changeCtx (Up:p) (CtxBlock ds:k, s)     = do
  fds <- assocMapM freeD ds
  changeCtx p (k, SBlock fds s)
changeCtx (Up:p) (CtxVLDecl x τ b:k, s) = free False b >> changeCtx p (k, SVLDecl x τ s)
changeCtx (Up:p) (CtxCompL s2:k, s1)    = changeCtx p (k, SComp s1 s2)
changeCtx (Up:p) (CtxCompR s1:k, s2)    = changeCtx p (k, SComp s1 s2)
changeCtx (Up:p) (CtxIfT e sf:k, st)    = changeCtx p (k, SIf e st sf)
changeCtx (Up:p) (CtxIfF e st:k, sf)    = changeCtx p (k, SIf e st sf)
changeCtx (Up:p) (CtxSwitch e:k, s)     = changeCtx p (k, SSwitch e s)
changeCtx (Up:p) (CtxLabel l:k, s)      = changeCtx p (k, SLabel l s)
changeCtx (Up:p) (CtxCase c:k, s)       = changeCtx p (k, SCase c s)
changeCtx (Up:p) (CtxLoop:k, s)         = changeCtx p (k, SLoop s)
changeCtx (Up:p) (CtxSetTrap t:k, s)    = changeCtx p (k, SSetTrap t s)
changeCtx (Down 0:p) (k, SBlock ds s)   = do
  ads <- assocMapM allocD ds
  changeCtx p (CtxBlock ads:k, s)
changeCtx (Down 0:_) (_, SVLDecl _ _ _) = mzero --jumping into a VLA block is undefined
changeCtx (Down 0:p) (k, SComp s1 s2)   = changeCtx p (CtxCompL s2:k, s1)
changeCtx (Down 1:p) (k, SComp s1 s2)   = changeCtx p (CtxCompR s1:k, s2)
changeCtx (Down 0:p) (k, SIf e st sf)   = changeCtx p (CtxIfT e sf:k, st)
changeCtx (Down 1:p) (k, SIf e st sf)   = changeCtx p (CtxIfF e st:k, sf)
changeCtx (Down 0:p) (k, SSwitch e s)   = changeCtx p (CtxSwitch e:k, s)
changeCtx (Down 0:p) (k, SLabel l s)    = changeCtx p (CtxLabel l:k, s)
changeCtx (Down 0:p) (k, SCase c s)     = changeCtx p (CtxCase c:k, s)
changeCtx (Down 0:p) (k, SLoop s)       = changeCtx p (CtxLoop:k, s)
changeCtx (Down 0:p) (k, SSetTrap t s)  = changeCtx p (CtxSetTrap t:k, s)
changeCtx _          _                  = mzero

next :: (MonadPlus m, MemWriter m) => SInCtx -> m (Maybe SInCtx)
next (k',s') = case next' k' of
  Just p  -> Just <$> changeCtx p (k',s')
  Nothing -> return Nothing
 where
  next' :: SCtx -> Maybe Path
  next' []             = Nothing
  next' (CtxCompL _:_) = Just [Up,Down 1]
  next' (CtxLoop:_)    = Just []
  next' (_:k)          = (Up:) <$> next' k

toTrap :: (MonadPlus m, MemWriter m) => Trap -> SInCtx -> m SInCtx
toTrap t (k',s') = do
  p <- maybeZero (toTrap' k')
  changeCtx p (k',s')
 where
  toTrap' :: SCtx -> Maybe Path
  toTrap' []                = Nothing
  toTrap' (CtxSetTrap t':k) = if t == t' then Just [] else (Up:) <$> toTrap' k
  toTrap' (_:k)             = (Up:) <$> toTrap' k

toLabel :: (MonadPlus m, MemWriter m) => Id -> SInCtx -> m SInCtx
toLabel l (k',s') = do
  p <- maybeZero (down s' `mplus` up k')
  changeCtx p (k',s')
 where
  down :: Stmt -> Maybe Path
  down (SBlock _ s)    = (Down 0:) <$> down s
  down (SVLDecl _ _ s) = (Down 0:) <$> down s
  down (SComp sl sr)   = ((Down 0:) <$> down sl) `mplus` ((Down 1:) <$> down sr)
  down (SIf _ st sf)   = ((Down 0:) <$> down st) `mplus` ((Down 1:) <$> down sf)
  down (SSwitch _ s)   = (Down 0:) <$> down s
  down (SLoop s)       = (Down 0:) <$> down s
  down (SLabel l' s)   = if l == l' then Just [] else (Down 0:) <$> down s
  down (SCase _ s)     = (Down 0:) <$> down s
  down (SSetTrap _ s)  = (Down 0:) <$> down s
  down _               = Nothing

  up :: SCtx -> Maybe Path
  up []              = Nothing
  up (CtxCompL sr:k) = ((Up:).(Down 1:) <$> down sr) `mplus` ((Up:) <$> up k)
  up (CtxCompR sl:k) = ((Up:).(Down 0:) <$> down sl) `mplus` ((Up:) <$> up k)
  up (CtxIfT _ sf:k) = ((Up:).(Down 1:) <$> down sf) `mplus` ((Up:) <$> up k)
  up (CtxIfF _ st:k) = ((Up:).(Down 0:) <$> down st) `mplus` ((Up:) <$> up k)
  up (CtxSwitch _:k) = (Up:) <$> up k
  up (CtxLabel l':k) = if l == l' then Just [] else (Up:) <$> up k
  up (CtxCase _:k)   = (Up:) <$> up k
  up (_:k)           = (Up:) <$> up k

toCase :: (MonadPlus m, MemWriter m) => Integer -> SInCtx -> m SInCtx
toCase c (k',s') = do
  p <- maybeZero (toCase' (Just c) s' `mplus` toCase' Nothing s')
  changeCtx p (k',s')
 where
  toCase' :: Maybe Integer -> Stmt -> Maybe Path
  toCase' mc (SBlock _ s)    = (Down 0:) <$> toCase' mc s
  toCase' mc (SVLDecl _ _ s) = (Down 0:) <$> toCase' mc s
  toCase' mc (SComp sl sr)   = ((Down 0:) <$> toCase' mc sl) `mplus` ((Down 1:) <$> toCase' mc sr)
  toCase' mc (SIf _ st sf)   = ((Down 0:) <$> toCase' mc st) `mplus` ((Down 1:) <$> toCase' mc sf)
  toCase' _  (SSwitch _ _)   = Nothing
  toCase' mc (SLoop s)       = (Down 0:) <$> toCase' mc s
  toCase' mc (SLabel _ s)    = (Down 0:) <$> toCase' mc s
  toCase' mc (SCase mc' s)   = if mc == mc' then Just [] else (Down 0:) <$> toCase' mc s
  toCase' mc (SSetTrap _ s)  = (Down 0:) <$> toCase' mc s
  toCase' _  _               = Nothing

toTop :: (MonadPlus m, MemWriter m) => SInCtx -> m SInCtx
toTop (k,s) = changeCtx (toTop' k) (k, s)
 where
  toTop' :: SCtx -> Path
  toTop' = fmap (\_ -> Up)

{- Expression in statement contexts -}
data EInS :: * -> * where
  CtxVLDeclT :: Id -> Stmt -> TInS
  CtxExpr    :: RInS
  CtxReturn  :: RInS
  CtxIfE     :: Stmt -> Stmt -> RInS
  CtxSwitchE :: Stmt -> RInS

type TInS = EInS Type
type RInS = EInS RVal

deriving instance Eq (EInS b)
deriving instance Show (EInS b)

instance Ord (EInS b) where
  CtxVLDeclT x r <= CtxVLDeclT y s = if x /= y then x <= y else r <= s
  CtxExpr        <= _              = True
  _              <= CtxExpr        = False
  CtxReturn      <= _              = True
  _              <= CtxReturn      = False
  CtxIfE r1 r2   <= CtxIfE s1 s2   = if r1 /= s1 then r1 <= s1 else r2 <= s2
  CtxIfE _ _     <= _              = True
  _              <= CtxIfE _ _     = False
  CtxSwitchE r   <= CtxSwitchE s   = r <= s
  CtxSwitchE _   <= _              = True
  _              <= CtxSwitchE _   = False  

-- dead code
instance Subst (EInS b) (Expr b) Stmt where
  subst (CtxVLDeclT x s) τ = SVLDecl x τ s
  subst CtxExpr          r = SExpr r
  subst CtxReturn        r = SReturn (Just r)
  subst (CtxIfE s1 s2)   r = SIf r s1 s2
  subst (CtxSwitchE s)   r = SSwitch r s

data EInSCtx b = EInSCtx {
  eCtx  :: SCtx,
  eInS  :: EInS b,
  eExpr :: Expr b, -- the original expression
  eTmps :: [Block]
} deriving (Eq, Show, Ord)

ctxVLDeclT :: SCtx -> Id -> VLType -> Stmt -> EInSCtx Type
ctxVLDeclT k x τ s = EInSCtx k (CtxVLDeclT x s) τ []

ctxExpr :: SCtx -> RExpr -> EInSCtx RVal
ctxExpr k r = EInSCtx k CtxExpr r []

ctxReturn :: SCtx -> RExpr -> EInSCtx RVal
ctxReturn k r = EInSCtx k CtxReturn r []

ctxIfE :: SCtx -> RExpr -> Stmt -> Stmt -> EInSCtx RVal
ctxIfE k r st sf = EInSCtx k (CtxIfE st sf) r []

ctxSwitchE :: SCtx -> RExpr -> Stmt -> EInSCtx RVal
ctxSwitchE k r s = EInSCtx k (CtxSwitchE s) r []

