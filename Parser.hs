{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XTypeSynonymInstances #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XTupleSections #-}

{-
Missing:
* null pointers
* Type checking at many places
* Proper error handling
* Checking for duplicate labels
* Initialisers
-}
module Parser where

import Util
import CSemantics
import Data.Maybe
import Data.List hiding (insert)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad
import Control.Applicative
import Control.Monad.Maybe
import Control.Monad.Error
import Control.Monad.State
import Language.C hiding (Error)

class (Monad m, Functor m) => ScopeMonad m where
  openScope :: m ()
  closeScope :: m ()
instance ScopeMonad m => ScopeMonad (MaybeT m) where
  openScope = lift openScope
  closeScope = lift closeScope
instance (ScopeMonad m, Error e) => ScopeMonad (ErrorT e m) where
  openScope = lift openScope
  closeScope = lift closeScope

data PDecl = PAuto Type | PAutoVL VLType | PStatic Block deriving (Eq, Show)

data Scope = Scope {
  sStructRename :: Assoc Id (StructUnion,Id),
  sDecls :: Assoc Id PDecl
} deriving (Eq, Show)

newScope :: Scope
newScope = Scope [] []

data PFun = PFun {
  pFunArgs :: Assoc Id Type,
  pFunType :: Type,
  pFunStmt :: Maybe Stmt
} deriving (Eq, Show)

{- Pre-states -}
data PreCState = PreCState {
  pMem :: Mem,
  pStructFields :: Map Id [Id],
  pFuns :: Map Id PFun,
  pScopes :: [Scope],
  pStructCounter :: Int
} deriving (Eq, Show)

instance MemReader (State PreCState) where
  getMem = gets pMem
instance MemWriter (State PreCState) where
  setMem m = modify $ \s -> s { pMem = m }
instance ScopeMonad (State PreCState) where
  openScope = modify $ \s -> s { pScopes = newScope:pScopes s }
  closeScope = modify $ \s -> s { pScopes = tail (pScopes s) }

type PreCMonad = ErrorT String (State PreCState)
type PreCMaybe = MaybeT (State PreCState)

emptyPreCState :: PreCState
emptyPreCState = PreCState emptyMem Map.empty Map.empty [newScope] 0

runPreCMonad :: PreCMonad a -> PreCState -> (Either String a, PreCState)
runPreCMonad m s = runState (runErrorT m) s

runPreCMonad_ :: PreCMonad a -> (Either String a, PreCState)
runPreCMonad_ m = runPreCMonad m emptyPreCState

pGetGlobalVars :: PreCState -> Either String (Map Id Block)
pGetGlobalVars st = case pScopes st of
  [Scope _ ds] -> return (Map.fromList (mapMaybe f ds))
  _            -> throwError "multiple scopes open"
 where
  f (x,PStatic b) = Just (x,b)
  f _             = Nothing

pGetFuns :: PreCState -> Either String (Map Id Fun)
pGetFuns st = Map.foldrWithKey f (return Map.empty) (pFuns st)
 where
  f x (PFun xs τ (Just s)) fs = Map.insert x (Fun xs τ s) <$> fs
  f _ (PFun _  _ Nothing)  _  = throwError "incomplete function"

toCState :: PreCState -> Either String CState
toCState st = do
  gs <- pGetGlobalVars st
  fs <- pGetFuns st
  return (CState (pMem st) fs gs [])

pGetFun :: Id -> PreCMaybe PFun
pGetFun x = gets pFuns >>= maybeT . Map.lookup x

pGetDecl :: Id -> PreCMaybe PDecl
pGetDecl x = gets pScopes >>= maybeT . foldr (mplus . lookup x . sDecls) Nothing

pVarType :: Id -> PreCMaybe VLType
pVarType x = pGetDecl x >>= f
 where
  f :: PDecl -> PreCMaybe VLType
  f (PAuto τ)     = return (VLType τ)
  f (PAutoVL τvl) = return τvl
  f (PStatic b)   = VLType <$> typeOfBlock b

pConstExpr :: Expr a -> PreCMaybe a
pConstExpr = constExpr $ \x -> do PStatic b <- pGetDecl x; return b

getScope :: PreCMaybe Scope
getScope = do s:_ <- gets pScopes; return s

setScope :: Scope -> PreCMaybe ()
setScope s = do _:ss <- gets pScopes; modify $ \st -> st { pScopes = s:ss }

pNewFun :: Id -> Assoc Id Type -> Type -> PreCMaybe ()
pNewFun x xs τ = do
  fs <- gets pFuns
  guard (x `Map.notMember` fs)
  modify $ \st -> st { pFuns = Map.insert x (PFun xs τ Nothing) fs }

pStoreFun :: Id -> Stmt -> PreCMaybe ()
pStoreFun x s = do
  PFun xs τ Nothing <- pGetFun x
  modify $ \st -> st { pFuns = Map.insert x (PFun xs τ (Just s)) (pFuns st) }

pNewDecl :: Id -> PDecl -> PreCMaybe ()
pNewDecl x d = do
  Scope rs vs <- getScope
  vs' <- maybeT (insert x d vs)
  setScope (Scope rs vs')

pStructRename :: Id -> PreCMaybe (StructUnion, Id)
pStructRename s = gets pScopes >>= maybeT . foldr (mplus . lookup s . sStructRename) Nothing

pGetStruct :: StructUnion -> Id -> PreCMaybe Id
pGetStruct su s = do
  (su',s') <- pStructRename s
  guard (su' == su)
  return s'

pFreshStruct :: Maybe Id -> State PreCState Id
pFreshStruct ms = 
  let s = maybe "anonymous" id ms in do
  n <- gets pStructCounter
  modify $ \st -> st { pStructCounter = n+1 }
  return (s ++ show n)

pNewStruct :: StructUnion -> Maybe Id -> PreCMaybe Id
pNewStruct su (Just s) = do
  Scope rs vs <- getScope
  case lookup s rs of
    Just (su',s') -> guard (su' == su) >> return s'
    Nothing       -> do
      s' <- lift (pFreshStruct (Just s))
      setScope (Scope (insertUnsafe s (su,s') rs) vs)
      return s'
pNewStruct _  Nothing = lift (pFreshStruct Nothing)
  
pStoreStruct :: StructUnion -> Id -> Assoc Id Type -> PreCMaybe ()
pStoreStruct su s fs = do
  modify $ \st -> st { pStructFields = Map.insert s xs (pStructFields st) }
  modifyMem $ \m -> m { memEnv = insertUnsafe (su,s) τs (memEnv m) }
 where xs = fst <$> fs; τs = snd <$> fs

scopeDecls :: PreCMonad (Assoc Id Decl)
scopeDecls = do Scope _ vs:_ <- gets pScopes; foldl f (return []) vs
 where
  f :: PreCMonad (Assoc Id Decl) -> (Id, PDecl) -> PreCMonad (Assoc Id Decl)
  f ds (x, PAuto τ)   = insertUnsafe x (DAuto τ) <$> ds
  f ds (_, PAutoVL _) = ds
  f ds (x, PStatic b) = insertUnsafe x (DStatic b) <$> ds

pFields :: Id -> PreCMaybe [Id]
pFields s = getsMaybe (Map.lookup s . pStructFields)

pFieldIndex :: Id -> Id -> PreCMaybe Int
pFieldIndex s x = pFields s >>= maybeT . elemIndex x

{- Pre-expressions -}
data PExpr =
  PAssign PExpr PExpr |
  PCall Id [PExpr] |
  PInt Integer |
  PVar Id |
  PDeref PExpr |
  PAddrOf PExpr |
  PField Id PExpr |
  PBinOp BinOp PExpr PExpr |
  PUnOp UnOp PExpr |
  PPreOp BinOp PExpr PExpr |
  PPostOp BinOp PExpr PExpr |
  PCast VLType PExpr |
  PIf PExpr PExpr PExpr |
  PComma PExpr PExpr
  deriving (Eq, Show)

pTrue :: PExpr
pTrue = PInt (boolToInt True)

pFalse :: PExpr
pFalse = PInt (boolToInt False)

pAnd :: PExpr -> PExpr -> PExpr
pAnd r1 r2 = PIf r1 (PIf r2 pTrue pFalse) pFalse

pOr :: PExpr -> PExpr -> PExpr
pOr r1 r2 = PIf r1 pTrue (PIf r2 pTrue pFalse)

binOpCast :: BinOp -> PExpr -> PExpr -> Maybe (PExpr,PExpr)
binOpCast = undefined

pToRExpr :: PExpr -> PreCMonad (RExpr,Type)
pToRExpr (PCall x es)    = do
  PFun xs τ _ <- tryT ("function " ++ show x ++ " does not exist") (pGetFun x)
  unless (length xs == length es) $
    throwError (show (length es) ++ " instead of " ++ show (length xs) ++ " arguments to " ++ show x)
  rs <- mapM f (zipWith (\(y,τy) ey -> (y,τy,ey)) xs es)
  return (ECall x rs, τ)
 where
  f :: (Id,Type,PExpr) -> PreCMonad RExpr
  f (y,τy,ey) = do
    (ry,τy') <- pToRExpr ey
    unless (τy' == τy) $
      throwError ("argument " ++ show y ++ " of " ++ show x ++ "is of " ++ show τy' ++ " instead of " ++ show τy)
    return ry
pToRExpr (PAssign e1 e2) = do
  (l,τl) <- pToLExpr e1
  (r,τr) <- pToRExpr e2
  unless (τl == τr) $ throwError ("assignment of " ++ show τr ++ " to " ++ show τl)
  return (EAssign l r, τr)
pToRExpr (PInt i)        = return (EVal (VInt i), TInt)
pToRExpr (PAddrOf e)     = do
  (l,τ) <- pToLExpr e
  return (EAddrOf l, TPointer τ)
pToRExpr p@(PField i e)  = ll `mplus` do
  (r,TStruct su s) <- pToRExpr e
  j <- tryT (show i ++ " is not a field of " ++ show s) (pFieldIndex s i)
  τj <- tryT (show i ++ " is not a field of " ++ show s) (fieldM su s j)
  return (EField su j r, arrayToPointer τj)
 where
  ll = do (l,τ) <- pToLExpr p; return (EToVal l, arrayToPointer τ)
pToRExpr (PBinOp op e1 e2) = do
  (r1,τ1) <- pToRExpr e1
  (r2,τ2) <- pToRExpr e2
  τ <- try (show τ1 ++ " and " ++ show τ2 ++ " for " ++ show op) (typeBinOp op τ1 τ2)
  return (EBinOp op r1 r2, τ)
pToRExpr (PUnOp op e)   = do
  (r,τ) <- pToRExpr e
  return (EUnOp op r, τ)
pToRExpr (PPreOp op e1 e2) = do
  (l,τl) <- pToLExpr e1
  (r,τr) <- pToRExpr e2
  τ <- try (show τl ++ " and " ++ show τr ++ " for pre-" ++ show op) (typeBinOp op τl τr)
  unless (τ == τl) $ throwError ("incorrect type for pre-" ++ show op)
  return (EPreOp op l r, τ)
pToRExpr (PPostOp op e1 e2) = do
  (l,τl) <- pToLExpr e1
  (r,τr) <- pToRExpr e2
  τ <- try (show τl ++ " and " ++ show τr ++ " for post-" ++ show op) (typeBinOp op τl τr)
  unless (τ == τl) $ throwError ("incorrect type for post-" ++ show op)
  return (EPostOp op l r, τ)
pToRExpr (PCast τ e)    = do
  (r,_) <- pToRExpr e
  return (ECast τ r, vlErase τ)
pToRExpr (PIf e1 e2 e3) = do
  (r1,τ1) <- pToRExpr e1
  unless (isScalar τ1) $ 
    throwError ("condition of if should be a scalar, but " ++ show e1 ++ " given")
  (r2,τ2) <- pToRExpr e2
  (r3,τ3) <- pToRExpr e3
  guard (τ2 == τ3)
  return (EIf r1 r2 r3, τ2)
pToRExpr (PComma e1 e2) = do
  (r1,_) <- pToRExpr e1
  (r2,τ2) <- pToRExpr e2
  return (EComma r1 r2, τ2)
pToRExpr e              = do
  (l,τ) <- pToLExpr e
  return (EToVal l, arrayToPointer τ)

pToLExpr :: PExpr -> PreCMonad (LExpr,Type)
pToLExpr (PVar x)       = do
  τ <- tryT ("variable " ++ show x ++ "not declared") (pVarType x)
  return (EVar x, vlErase τ)
pToLExpr (PDeref e)     = do
  (r,τp) <- pToRExpr e
  τ <- try ("deref expects pointer, but " ++ show e ++ "given") (stripPointer τp)
  when (isVoid τ) $ throwError "deref of void pointer"
  return (EDeref r, τ)
pToLExpr (PField i e)   = do
  (l,TStruct su s) <- pToLExpr e
  j <- tryT (show i ++ " is not a field of " ++ show s) (pFieldIndex s i)
  τj <- tryT (show i ++ " is not a field of " ++ show s) (fieldM su s j)
  return (ELField su j l, τj)
pToLExpr e              = throwError (show e ++ " cannot be used as L-expression")

{- From Language.C -}
cToStructUnion :: CStructTag  -> StructUnion
cToStructUnion CStructTag = Struct
cToStructUnion CUnionTag  = Union

cConstToPExpr :: CConst -> PreCMonad PExpr
cConstToPExpr (CIntConst i _) = return (PInt (getCInteger i))
cConstToPExpr e               = throwError (show e ++ " not supported")

cToBinOp :: CBinaryOp -> PExpr -> PExpr -> PExpr
cToBinOp CAddOp = PBinOp PlusOp
cToBinOp CSubOp = PBinOp MinusOp
cToBinOp CMulOp = PBinOp MultOp
cToBinOp CDivOp = PBinOp DivOp
cToBinOp CRmdOp = PBinOp RemOp
cToBinOp CShlOp = PBinOp ShiftLOp
cToBinOp CShrOp = PBinOp ShiftROp
cToBinOp CLeqOp = PBinOp LeOp
cToBinOp CLeOp  = PBinOp LtOp
cToBinOp CGeqOp = PBinOp GeOp
cToBinOp CGrOp  = PBinOp GtOp
cToBinOp CEqOp  = PBinOp EqOp
cToBinOp CNeqOp = PBinOp NeOp
cToBinOp CAndOp = PBinOp BitAndOp
cToBinOp COrOp  = PBinOp BitOrOp
cToBinOp CXorOp = PBinOp BitXorOp
cToBinOp CLndOp = pAnd
cToBinOp CLorOp = pOr

cToUnOp :: CUnaryOp -> PExpr -> PExpr
cToUnOp CPreIncOp  = \e -> PPreOp PlusOp e (PInt 1)
cToUnOp CPreDecOp  = \e -> PPreOp MinusOp e (PInt 1)
cToUnOp CPostIncOp = \e -> PPostOp PlusOp e (PInt 1)
cToUnOp CPostDecOp = \e -> PPostOp MinusOp e (PInt 1)
cToUnOp CAdrOp     = PAddrOf
cToUnOp CIndOp     = PDeref
cToUnOp CPlusOp    = id
cToUnOp CMinOp     = PUnOp NegOp
cToUnOp CCompOp    = PUnOp CompOp
cToUnOp CNegOp     = PUnOp NotOp

cToAssign :: CAssignOp -> PExpr -> PExpr -> PExpr
cToAssign CAssignOp = PAssign
cToAssign CMulAssOp = PPreOp MultOp
cToAssign CDivAssOp = PPreOp DivOp
cToAssign CRmdAssOp = PPreOp RemOp
cToAssign CAddAssOp = PPreOp PlusOp
cToAssign CSubAssOp = PPreOp MinusOp
cToAssign CShlAssOp = PPreOp ShiftLOp
cToAssign CShrAssOp = PPreOp ShiftROp
cToAssign CAndAssOp = PPreOp BitAndOp
cToAssign CXorAssOp = PPreOp BitXorOp
cToAssign COrAssOp  = PPreOp BitOrOp

{- Expressions -}
cToPExpr :: CExpr -> PreCMonad PExpr
cToPExpr (CComma [] _)             = throwError "empty comma expression"
cToPExpr (CComma es _)             = foldr1 PComma <$> sequence (cToPExpr <$> es)
cToPExpr (CConst c)                = cConstToPExpr c
cToPExpr (CVar x _)                = return (PVar (identToString x))
cToPExpr (CUnary op e _)           = cToUnOp op <$> cToPExpr e
cToPExpr (CIndex e1 e2 _)          = PDeref <$> (PBinOp PlusOp <$> cToPExpr e1 <*> cToPExpr e2)
cToPExpr (CMember e i d _)         = PField (identToString i) . (if d then PDeref else id) <$> cToPExpr e
cToPExpr (CBinary op e1 e2 _)      = cToBinOp op <$> cToPExpr e1 <*> cToPExpr e2
cToPExpr (CCond e1 (Just e2) e3 _) = PIf <$> cToPExpr e1 <*> cToPExpr e2 <*> cToPExpr e3
cToPExpr (CCast τ e _)             = PCast <$> cDeclToType τ <*> cToPExpr e
cToPExpr (CCompoundLit _ _ _)      = throwError "compound literal not supported"
cToPExpr (CAssign as e1 e2 _)      = cToAssign as <$> cToPExpr e1 <*> cToPExpr e2
cToPExpr (CCall (CVar x _) es _)   = PCall (identToString x) <$> sequence (cToPExpr <$> es)
cToPExpr e                         = throwError (show e ++ " not supported")

cToRExpr :: CExpr -> PreCMonad (RExpr,Type)
cToRExpr e = do
  (r,τ) <- cToPExpr e >>= pToRExpr
  -- unless (isSafe r) $ throwError "expression with multiple side effects"
  return (r,τ)

cToRExpr_ :: CExpr -> PreCMonad RExpr
cToRExpr_ = fmap fst . cToRExpr

cToRScalar :: CExpr -> PreCMonad RExpr
cToRScalar e = do 
  (r,τ) <- cToRExpr e
  unless (isScalar τ) $ throwError "scalar expected"
  return r

{- Types -}
cStructUnionToType :: CStructUnion -> PreCMonad Type
cStructUnionToType (CStruct su (Just s) Nothing _ _) =
  let su' = cToStructUnion su in do
  s' <- tryT "struct/union not declared" (pGetStruct su' (identToString s))
  return (TStruct su' s')
cStructUnionToType (CStruct _ Nothing Nothing _ _)   = throwError "struct/union without name and fields"
cStructUnionToType (CStruct su ms (Just ds) _ _)     = 
  let su' = cToStructUnion su in do
  s' <- tryT "struct/union not fresh" (pNewStruct su' (identToString <$> ms))
  fds <- foldCDecls f (return []) ds
  when (length fds == 0) $ throwError "struct/union with empty field list"
  tryT "failed to store struct/union" (pStoreStruct su' s' fds)
  return (TStruct su' s')
 where
  f :: Maybe (Id, Storage) -> VLType -> Maybe RExpr -> PreCMonad (Assoc Id Type) -> PreCMonad (Assoc Id Type)
  f Nothing           _   _        _  = throwError "nameless struct/union field"
  f (Just (x,Auto))   τvl Nothing  τs = do
    τ <- try "VL type in struct/union field" (constExpr_ τvl)
    τs >>= try "struct/union member not fresh" . insert x τ
  f (Just (_,Static)) _   _        _  = throwError "static in struct/union"
  f _                 _   (Just _) _  = throwError "initialiser in struct/union"

cTypeSpecToType :: [CTypeSpec] -> PreCMonad Type
cTypeSpecToType []                  = throwError "invalid type spec"
cTypeSpecToType (CIntType _:_)      = return TInt
cTypeSpecToType (CShortType _:l)    = cTypeSpecToType l
cTypeSpecToType (CLongType _:l)     = cTypeSpecToType l
cTypeSpecToType (CFloatType _:_)    = throwError "float not supported"
cTypeSpecToType (CDoubleType _:_)   = throwError "double not supported"
cTypeSpecToType (CSignedType _:l)   = cTypeSpecToType l
cTypeSpecToType (CUnsigType _:l)    = cTypeSpecToType l
cTypeSpecToType (CBoolType _:_)     = throwError "bool not supported"
cTypeSpecToType (CComplexType _:_)  = throwError "complex not supported"
cTypeSpecToType (CSUType s _:_)     = cStructUnionToType s
cTypeSpecToType (CEnumType _ _:_)   = throwError "enum not supported"
cTypeSpecToType (CTypeDef _ _:_)    = throwError "typedef not supported"
cTypeSpecToType (CTypeOfExpr _ _:_) = throwError "typeof not supported"
cTypeSpecToType (CTypeOfType _ _:_) = throwError "typeof not supported"
cTypeSpecToType (CVoidType _:_)     = return TVoid
cTypeSpecToType (CCharType _:_)     = throwError "char not supported"

cInitToRExpr :: VLType -> CInit -> PreCMonad RExpr
cInitToRExpr τvl (CInitExpr e _) = do
  (r,τ) <- cToRExpr e
  unless (τ == vlErase τvl) $ throwError "initialiser of incorrect type"
  return r    
cInitToRExpr _   (CInitList _ _) = throwError "compound initialiser not supported"

cAddDerivedDeclr' :: Type -> [CDerivedDeclr] -> PreCMonad VLType
cAddDerivedDeclr' τ []                               = return (VLType τ)
cAddDerivedDeclr' τ (CPtrDeclr _ _:l)                = VLPointer <$> cAddDerivedDeclr' τ l
cAddDerivedDeclr' τ (CArrDeclr _ (CArrSize _ e) _:l) = do
  (pe,τe) <- cToRExpr e
  unless (isInteger τe) $ throwError "error size should be an integer"
  τl <- cAddDerivedDeclr' τ l
  return (VLArray τl pe)
cAddDerivedDeclr' _ (CArrDeclr _ (CNoArrSize _) _:_) = throwError "arrays of unknown size not supported"
cAddDerivedDeclr' _ (CFunDeclr _ _ _:_)              = throwError "function declarator not supported"

cAddDerivedDeclr :: Type -> [CDerivedDeclr] -> PreCMonad VLType
cAddDerivedDeclr τ l = do
  τvl <- cAddDerivedDeclr' τ l
  e <- getEnv
  unless (checkType e (vlErase τvl)) $ throwError "invalid type"
  return τvl

cDeclSpecsToType :: [CDeclSpec] -> PreCMonad (Storage, Type)
cDeclSpecsToType l = (,) <$> cToStorage ss <*> cTypeSpecToType tss
 where (ss,_,_,tss,_) = partitionDeclSpecs l

data Storage = Auto | Static deriving (Eq, Show)

cToStorage :: [CStorageSpec] -> PreCMonad Storage
cToStorage []          = return Auto
cToStorage [CAuto _]   = return Auto
cToStorage [CStatic _] = return Static
cToStorage c           = throwError (show c ++ " not supported")

foldCDecl :: (Maybe (Id, Storage) -> VLType -> Maybe RExpr -> PreCMonad a -> PreCMonad a)
  -> PreCMonad a -> CDecl -> PreCMonad a
foldCDecl k a (CDecl dss [] _)  = do
  (sto,τ) <- cDeclSpecsToType dss
  when (sto == Static) $ throwError "anonymous declaration cannot be static"
  k Nothing (VLType τ) Nothing a
foldCDecl k a (CDecl dss drs _) = do
  (s,τ) <- cDeclSpecsToType dss
  foldr (\ds m -> case ds of
    (Nothing, _, _)                        -> k Nothing (VLType τ) Nothing m
    (Just (CDeclr mx l _ _ _), me, _) -> do
      τvl <- cAddDerivedDeclr τ l
      mr <- maybeMapM (cInitToRExpr τvl) me
      k ((,s) <$> identToString <$> mx) τvl mr m
   ) a drs

foldCDecls :: (Maybe (Id, Storage) -> VLType -> Maybe RExpr -> PreCMonad a -> PreCMonad a) 
  -> PreCMonad a -> [CDecl] -> PreCMonad a
foldCDecls k a = foldr (flip (foldCDecl k)) a
  
cDeclToType :: CDecl -> PreCMonad VLType
cDeclToType d = do
  τs <- foldCDecl f (return []) d
  case τs of [τ] -> return τ; _ -> throwError "multiple declrs in type"
 where
  f :: Maybe (Id, Storage) -> VLType -> Maybe RExpr -> PreCMonad [VLType] -> PreCMonad [VLType]
  f Nothing  τ Nothing  τs = (τ:) <$> τs
  f (Just _) _ _        _  = throwError "ident in type"
  f _        _ (Just _) _  = throwError "initialiser in type"

{- Statement -}
cBlockItemsToStmt :: [CBlockItem] -> PreCMonad Stmt
cBlockItemsToStmt []                = return SSkip
cBlockItemsToStmt (CBlockStmt s:bs) = SComp <$> cToStmt s <*> cBlockItemsToStmt bs
cBlockItemsToStmt (CBlockDecl d:bs) = cDeclToStmt d (cBlockItemsToStmt bs)
cBlockItemsToStmt s                 = throwError (show s ++ " not supported")

cDeclToStmt :: CDecl -> PreCMonad Stmt -> PreCMonad Stmt
cDeclToStmt = flip (foldCDecl f)
 where
  f :: Maybe (Id, Storage) -> VLType -> Maybe RExpr -> PreCMonad Stmt -> PreCMonad Stmt
  f (Just (x,Auto)) τvl mr ms  = case constExpr_ τvl of
    Just τ  -> do
      tryT "variable not fresh" (pNewDecl x (PAuto τ))
      maybe id (SComp . SExpr . EAssign (EVar x)) mr <$> ms
    Nothing -> do
      tryT "variable not fresh" (pNewDecl x (PAutoVL τvl))
      -- initialization of a vla is only allowed in case it is a pointer
      -- for now, we cannot initialise arrays, so there should not be a problem
      SVLDecl x τvl <$> maybe id (SComp . SExpr . EAssign (EVar x)) mr <$> ms
  f (Just (x,Static)) τvl mr ms = do
    τ <- try "VL static" (constExpr_ τvl)
    mv <- tryT "non const static" (maybeMapM pConstExpr mr)
    b <- alloc τ (aVal <$> mv) MStatic
    tryT "variable not fresh" (pNewDecl x (PStatic b))
    ms
  f Nothing           _   _  _  = throwError "unnamed declaration"

cToStmt :: CStat -> PreCMonad Stmt
cToStmt (CExpr Nothing _)      = return SSkip
cToStmt (CExpr (Just e) _)     = SExpr <$> cToRExpr_ e
cToStmt (CCompound _ sds _)    = do
  openScope
  ss <- cBlockItemsToStmt sds
  ds <- scopeDecls
  closeScope
  return (SBlock ds ss)
cToStmt (CIf r s1 Nothing _)   = SIf <$> cToRScalar r <*> cToStmt s1 <*> return SSkip
cToStmt (CIf r s1 (Just s2) _) = SIf <$> cToRScalar r <*> cToStmt s1 <*> cToStmt s2
cToStmt (CSwitch r s _)        = sSwitch <$> cToRScalar r <*> cToStmt s
cToStmt (CWhile e s False _)   = sWhile <$> cToRExpr_ e <*> cToStmt s
cToStmt (CWhile e s True _)    = sDoWhile <$> cToStmt s <*> cToRExpr_ e
cToStmt (CFor e1 me2 me3 s _)  = case e1 of
  Left Nothing  -> s'
  Left (Just e) -> SComp <$> (SExpr <$> cToRExpr_ e) <*> s'
  Right d       -> cDeclToStmt d s'
 where
  s' = sFor <$> maybeMapM cToRScalar me2 <*> maybeMapM cToRExpr_ me3 <*> cToStmt s
cToStmt (CCont _)              = return sContinue
cToStmt (CBreak _)             = return sBreak
cToStmt (CReturn e _)          = SReturn <$> maybeMapM cToRExpr_ e -- the return value should have the return type
cToStmt (CLabel l s _ _)       = SLabel (identToString l) <$> cToStmt s -- l should be fresh in function scope
cToStmt (CCase r s _)          = do
  re <- cToRScalar r
  VInt n <- try "non constant expression in case" (constExpr_ re)
  SCase (Just n) <$> cToStmt s -- n should be fresh
cToStmt (CDefault s _)         = SCase Nothing <$> cToStmt s
cToStmt (CGoto l _)            = return (SGoto (identToString l)) -- l should exist in function scope
cToStmt s                      = throwError (show s ++ " not supported")

cTranslUnitToProg :: CTranslUnit -> PreCMonad ()
cTranslUnitToProg (CTranslUnit ds _) = cEDeclsToProg ds

cEDeclsToProg :: [CExtDecl] -> PreCMonad ()
cEDeclsToProg []               = return ()
cEDeclsToProg (CDeclExt d:eds) = foldCDecl f (cEDeclsToProg eds) d
 where 
  f :: Maybe (Id, Storage) -> VLType -> Maybe RExpr -> PreCMonad () -> PreCMonad ()
  f Nothing      τvl _  m = do
    _ <- try "global VL type" (constExpr_ τvl)
    m
  f (Just (x,_)) τvl mr m = do
    τ <- try "global of VL type" (constExpr_ τvl)
    mv <- tryT "non const global" (maybeMapM pConstExpr mr)
    b <- alloc τ (aVal <$> mv) MStatic
    tryT "global not fresh" (pNewDecl x (PStatic b))
    m
cEDeclsToProg (CFDefExt d:eds) = cToFun d >> cEDeclsToProg eds
cEDeclsToProg (CAsmExt _ _:_)  = throwError "asm not supported"

cToFun :: CFunDef -> PreCMonad ()
cToFun (CFunDef _   (CDeclr Nothing  _ _ _ _) _ _ _) = throwError "anonymous function"
cToFun (CFunDef dss (CDeclr (Just x) l _ _ _) _ s _) =
  case l of
    CFunDeclr (Right (ds,_)) _ _:l' -> do
      (_,τ) <- cDeclSpecsToType dss
      τvl <- cAddDerivedDeclr τ l'
      τf <- try "VL function" (constExpr_ τvl)
      xs <- cToFunArgs ds
      tryT "function already exists" (pNewFun (identToString x) xs τf)
      openScope
      tryT "modifying scope failed" (setScope (Scope [] (mapAssoc PAuto xs)))
      s' <- cToStmt s
      closeScope
      tryT "function already completed" (pStoreFun (identToString x) s')
    CFunDeclr (Left _)       _ _:_  -> throwError "old style functions not supported"
    _                               -> throwError "function of non-function type"

cToFunArgs :: [CDecl] -> PreCMonad (Assoc Id Type)
cToFunArgs [CDecl [CTypeSpec (CVoidType _)] _ _] = return []
cToFunArgs ds                                    = foldCDecls f (return []) ds
 where
  f :: Maybe (Id, Storage) -> VLType -> Maybe RExpr -> PreCMonad (Assoc Id Type) -> PreCMonad (Assoc Id Type)
  f Nothing        _   _  _   = throwError "anonymous function argument"
  f (Just (y,sto)) τvl me mxs = do
    when (sto == Static) $ throwError "static function argument"
    when (isJust me) $ throwError "function argument with initialiser"
    τ <- try "VL function argument" (constExpr_ τvl)
    mxs >>= try "duplicate function argument" . insert y (arrayToPointer τ)

