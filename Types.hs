{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XUndecidableInstances #-}
{-# OPTIONS -XFunctionalDependencies #-}

module Types where

import Util

import Data.Maybe
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Maybe
import Control.Monad.Error

{- Types -}
data StructUnion = Struct | Union deriving (Eq, Show, Ord)

data BType =
  TInt |
  TPointer Type deriving (Eq, Show, Ord) -- TPointer τ
data Type =
  TBase Bool BType | -- TBase const τ
  TVoid |
  TArray Type Int |
  TStruct StructUnion Bool Id deriving (Eq, Show, Ord) -- TStruct su const s

subType :: Type -> Type -> Bool
τ1 `subType` τ2 | τ1 == τ2 = True
τ1 `subType` TArray τ2 _   = τ1 `subType` τ2
_  `subType` _             = False

class BTypeOf a where
  bTypeOf :: a -> BType

class TypeOf a where
  typeOf :: a -> Type

class ConstOps a where
  isConst :: a -> Bool
  setConst :: Bool -> a -> a

makeConst :: ConstOps a => Bool -> a -> a
makeConst c = if c then setConst True else id

remConst :: ConstOps a => a -> a
remConst = setConst False

instance ConstOps Type where
  isConst TVoid           = False
  isConst (TBase c _)     = c
  isConst (TArray τ _)    = isConst τ
  isConst (TStruct _ c _) = c

  setConst _ TVoid            = TVoid
  setConst c (TBase _ τ)      = TBase c τ
  setConst c (TArray τ n)     = TArray (setConst c τ) n
  setConst c (TStruct su _ s) = TStruct su c s

{- Environments -}
type Env = Assoc (StructUnion,Id) [Type]

emptyEnv :: Env
emptyEnv = []

class (Functor m, Monad m) => EnvReader m where
  getEnv :: m Env
instance EnvReader m => EnvReader (MaybeT m) where
  getEnv = lift getEnv
instance (Error e, EnvReader m) => EnvReader (ErrorT e m) where
  getEnv = lift getEnv
instance EnvReader Identity where
  getEnv = return []

structExists :: EnvReader m => StructUnion -> Id -> m Bool
structExists su s = do e <- getEnv; return ((su,s) `inDom` e)
fields :: (EnvReader m, MonadPlus m) => StructUnion -> Bool -> Id -> m [Type]
fields su c s = do e <- getEnv; fmap (makeConst c) <$> maybeZero (lookup (su, s) e)
fieldsDefault :: EnvReader m => StructUnion -> Bool -> Id -> m [Type]
fieldsDefault su c s = fromMaybeT [] (fields su c s)
field :: (EnvReader m, MonadPlus m) => StructUnion -> Bool -> Id -> Int -> m Type
field su c s x = fields su c s >>= maybeZero . (!? x)

{- Well-formedness of types -}
checkBType :: Env -> BType -> Bool
checkBType _ TInt                       = True
checkBType _ (TPointer (TStruct _ _ _)) = True
checkBType e (TPointer τ)               = checkType e τ

checkType :: Env -> Type -> Bool
checkType _ TVoid            = True
checkType e (TBase _ τ)      = checkBType e τ
checkType e (TArray τ n)     = n >= 0 && checkType e τ
checkType e (TStruct su _ s) = (su,s) `inDom` e

checkEnv :: Env -> Bool
checkEnv []           = True
checkEnv ((sus,τs):e) = not (sus `inDom` e) && checkEnv e && all (checkType e) τs

class EnvReader m => Check m a | a -> m where
  check :: a -> m Bool

instance EnvReader m => Check m BType where
  check τ = do e <- getEnv; return (checkBType e τ)
instance EnvReader m => Check m Type where
  check τ = do e <- getEnv; return (checkType e τ)

{- Helper functions -}
isVoid :: Type -> Bool
isVoid TVoid = True
isVoid _     = False

stripPointer :: Type -> Maybe Type
stripPointer (TBase _ (TPointer τ)) = Just τ
stripPointer _                      = Nothing

isArray :: Type -> Bool
isArray (TArray _ _) = True
isArray _            = False

stripArray   :: Type -> Maybe Type
stripArray (TArray τ _) = Just τ
stripArray _            = Nothing

isInteger :: Type -> Bool
isInteger (TBase _ TInt) = True
isInteger _              = False

isScalar :: Type -> Bool
isScalar a = isInteger a || isJust (stripPointer a)

arrayToPointer :: Type -> Type
arrayToPointer a = maybe a (TBase False . TPointer) (stripArray a) -- const or not?

arrayBase :: Type -> Type
arrayBase (TArray τ _) = arrayBase τ
arrayBase τ            = τ

arrayWidth :: Type -> Int
arrayWidth (TArray τ n) = n * arrayWidth τ
arrayWidth _            = 1

isCompleteB :: EnvReader m => BType -> m Bool
isCompleteB TInt         = return True
isCompleteB (TPointer τ) = isComplete τ

-- This is incorrect, we should also check whether a struct's fields are
-- complete. But doing it the naive way yields a non-termination.
isComplete :: EnvReader m => Type -> m Bool
isComplete TVoid            = return False
isComplete (TBase _ τ)      = isCompleteB τ
isComplete (TArray τ n)     = return (n >= 1) &&? isComplete τ
isComplete (TStruct su _ s) = structExists su s

-- This terminates (for well formed types) because we do not recurse into a
-- pointer's type.
isModifiable :: EnvReader m => Type -> m Bool
isModifiable TVoid            = return True
isModifiable (TBase c _)      = return (not c)
isModifiable (TArray τ _)     = isModifiable τ
isModifiable (TStruct su c s) = do
  τs <- fieldsDefault su False s
  return (not c) &&? allM isModifiable τs

{- Common initial segment -}
cisList :: [Type] -> [Type] -> Int
cisList (τ:τs) (σ:σs) | τ == σ = 1 + cisList τs σs
cisList _ _                    = 0

cis :: EnvReader m => Id -> Id -> m Int
cis s1 s2 = liftM2 cisList (fieldsDefault Struct False s1) (fieldsDefault Struct False s2)

cisFields :: EnvReader m => Id -> Int -> Int -> m Int
cisFields u x1 x2 = fromMaybeT 0 $ do
  TStruct Struct _ s1 <- field Union False u x1
  TStruct Struct _ s2 <- field Union False u x2
  lift (cis s1 s2)

