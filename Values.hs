{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XStandaloneDeriving #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XGADTs #-}
{-# OPTIONS -XKindSignatures #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XUndecidableInstances #-}
{-# OPTIONS -XRankNTypes #-}
{-# OPTIONS -XFunctionalDependencies #-}

module Values where

import Util
import Types

import Prelude
import Control.Monad
import Control.Monad.Maybe
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Identity

class Defined v where
  undef :: BType -> v
  isDefined :: v -> Bool

isUndefined :: Defined v => v -> Bool
isUndefined = not . isDefined

class EnvReader m => Determinate m v where
  isDeterminate :: v -> m Bool

isIndeterminate :: Determinate m v => v -> m Bool
isIndeterminate = fmap not . isDeterminate

{- Base Values -}
data BVal p =
  VUndef BType |
  VInt Integer |
  VNULL Type |
  VPointer p deriving (Eq, Show)

instance Functor BVal where
  fmap _ (VUndef τ)   = VUndef τ
  fmap _ (VInt i)     = VInt i
  fmap _ (VNULL τ)    = VNULL τ
  fmap f (VPointer p) = VPointer (f p)

instance TypeOf p => BTypeOf (BVal p) where
  bTypeOf (VUndef τ)   = τ
  bTypeOf (VInt _)     = TInt
  bTypeOf (VNULL τ)    = TPointer τ
  bTypeOf (VPointer p) = TPointer (typeOf p)

instance Defined (BVal p) where
  undef                = VUndef
  isDefined (VUndef _) = False
  isDefined _          = True

instance Determinate m p => Determinate m (BVal p) where
  isDeterminate (VPointer p) = isDeterminate p
  isDeterminate v            = return (isDefined v)

zeroBVal :: BType -> BVal p
zeroBVal TInt         = VInt 0
zeroBVal (TPointer τ) = VNULL τ

instance Check m p => Check m (BVal p) where
  check (VUndef τ)   = check τ
  check (VInt _)     = return True
  check (VNULL τ)    = check τ
  check (VPointer p) = check p

{- Values -}
data Val a =
  VBase Bool a |
  VStruct Bool Id [AVal a] |
  VUnion Bool Id (Maybe (Int,AVal a)) deriving (Eq, Show)
data AVal a = VArray Type [Val a] deriving (Eq, Show)

isBase :: Val p -> Maybe p
isBase (VBase _ a) = Just a
isBase _           = Nothing

instance BTypeOf a => TypeOf (Val a) where
  typeOf (VBase c a)     = TBase c (bTypeOf a)
  typeOf (VStruct c s _) = TStruct Struct c s
  typeOf (VUnion c s _)  = TStruct Union c s

instance BTypeOf a => TypeOf (AVal a) where
  typeOf (VArray τ _)    = τ

instance (Check m a, BTypeOf a) => Check m (Val a) where
  check (VBase _ a)              = check a
  check (VStruct _ s vs)         = fromMaybeT False $ do
    τs <- fields Struct False s
    guard (length τs == length vs)
    allM (\(τ,v) -> return (typeOf v == τ) &&? lift (check v)) (zip τs vs)
  check (VUnion _ s Nothing)     = structExists Union s
  check (VUnion _ s (Just(i,v))) = fromMaybeT False $ do
    τ <- field Union False s i
    return (τ == typeOf v) &&? lift (check v)

instance (Check m a, BTypeOf a) => Check m (AVal a) where
  check (VArray τ vs) = return (length vs == arrayWidth τ) &&?
                         allM (\v -> return (typeOf v == arrayBase τ) &&? check v) vs

instance ConstOps (Val a) where
  isConst (VBase c _)     = c
  isConst (VStruct c _ _) = c
  isConst (VUnion c  _ _) = c

  setConst c (VBase _ a)      = VBase c a
  setConst c (VStruct _ s vs) = VStruct c s (setConst c <$> vs)
  setConst c (VUnion _ s v')  = VUnion c s (mapSnd (setConst c) <$> v')

instance ConstOps (AVal a) where
  isConst (VArray τ _)      = isConst τ
  setConst c (VArray τ vs)  = VArray τ (setConst c <$> vs)

instance Determinate m v => Determinate m (Val v) where
  isDeterminate (VBase _ v) = isDeterminate v
  isDeterminate _           = return True

instance Determinate m v => Determinate m (AVal v) where
  isDeterminate _ = return True

instance Functor Val where
  fmap f (VBase c a)      = VBase c (f a)
  fmap f (VStruct c s vs) = VStruct c s (fmap f <$> vs)
  fmap f (VUnion c s v')  = VUnion c s (mapSnd (fmap f) <$> v')

instance Functor AVal where
  fmap f (VArray τ vs)  = VArray τ (fmap f <$> vs)

infixr 5 +++

class SimpleReference r where
  branch  :: StructUnion -> Int -> r Val -> r AVal
  branchA :: Int -> r AVal -> r Val

class Reference (r :: (* -> *) -> (* -> *) -> *) where
  (+++)   :: r u v -> r v w -> r u w

vMapM :: (Monad m, SimpleReference r) => (r Val -> a -> m b) -> r Val -> Val a -> m (Val b)
vMapM f p (VBase c a)              = liftM (VBase c) (f p a)
vMapM f p (VStruct c s vs)         = do
  vs' <- iMapM (\i -> avMapM f (branch Struct i p)) 0 vs
  return (VStruct c s vs')
vMapM _ _ (VUnion c s Nothing)     = return (VUnion c s Nothing)
vMapM f p (VUnion c s (Just(i,v))) = do
  v' <- avMapM f (branch Union i p) v
  return (VUnion c s (Just(i,v')))

avMapM :: (Monad m, SimpleReference r) => (r Val -> a -> m b) -> r AVal -> AVal a -> m (AVal b)
avMapM f p (VArray τ vs)           = do
  vs' <- iMapM (\i -> vMapM f (branchA i p)) 0 vs
  return (VArray τ vs')

vMap :: SimpleReference r => (r Val -> a -> b) -> r Val -> Val a -> Val b
vMap f p = runIdentity . vMapM (\q -> Identity . f q) p

vFoldr :: SimpleReference r => (r Val -> a -> b -> b) -> b -> r Val -> Val a -> b
vFoldr f b p (VBase _ a)               = f p a b
vFoldr f b p (VStruct _ _ vs)          = iFoldr (\i a c -> avFoldr f c (branch Struct i p) a) b 0 vs
vFoldr _ b _ (VUnion _ _ Nothing)      = b
vFoldr f b p (VUnion _ _ (Just(i,vs))) = avFoldr f b (branch Union i p) vs

avFoldr :: SimpleReference r => (r Val -> a -> b -> b) -> b -> r AVal -> AVal a -> b
avFoldr f b p (VArray _ vs)            = iFoldr (\i a c -> vFoldr f c (branchA i p) a) b 0 vs

vTraverse :: (Monad m, SimpleReference r) => (r Val -> a -> m b) -> r Val -> Val a -> m ()
vTraverse f = vFoldr (\p a c -> f p a >> c) (return ())

avTraverse :: (Monad m, SimpleReference r) => (r Val -> a -> m b) -> r AVal -> AVal a -> m ()
avTraverse f = avFoldr (\p a c -> f p a >> c) (return ())

newVal :: EnvReader m => (BType -> a) -> Type -> MaybeT m (Val a)
newVal _    TVoid                = nothingT
newVal newB (TBase c τ)          = return (VBase c (newB τ))
newVal newB (TStruct Struct c s) = do
  τs <- fields Struct False s
  VStruct c s <$> sequence (newAVal newB <$> τs)
newVal _    (TStruct Union c s)  = return (VUnion c s Nothing)
newVal _    (TArray _ _)         = nothingT

newAVal :: EnvReader m => (BType -> a) -> Type -> MaybeT m (AVal a)
newAVal newB τ                   = VArray τ <$> replicate (arrayWidth τ) <$> newVal newB (arrayBase τ)

aVal :: BTypeOf a => Val a -> AVal a
aVal v = VArray (typeOf v) [v]

{- References -}
data Ref :: * -> (* -> *) -> (* -> *) -> * where
  RHere   :: Ref c v v
  RStruct :: Int -> Ref c AVal w -> Ref c Val w
  RUnion  :: c -> Int -> Ref c AVal w -> Ref c Val w
  RArray  :: Int -> Ref c Val w -> Ref c AVal w

deriving instance Eq c => Eq (Ref c v w)
deriving instance Show c => Show (Ref c v w)

class Eq c => Cis c where noCis :: c
instance Cis ()     where noCis = ()
instance Cis Bool   where noCis = False

rCisReset :: Cis d => Ref c v w -> Ref d v w
rCisReset RHere          = RHere
rCisReset (RStruct i p)  = RStruct i (rCisReset p)
rCisReset (RUnion _ i p) = RUnion noCis i (rCisReset p)
rCisReset (RArray i p)   = RArray i (rCisReset p)

target :: EnvReader m => Ref c v w -> Type -> MaybeT m Type
target RHere          τ                    = return τ
target (RStruct i p)  (TStruct Struct c s) = field Struct c s i >>= target p
target (RUnion _ i p) (TStruct Union c s)  = field Union c s i >>= target p
target (RArray i p)   τ                    = guard (0 <= i && i < arrayWidth τ) >> target p (arrayBase τ)
target _              _                    = nothingT

instance Reference (Ref c) where
  RHere         +++ p2 = p2
  RStruct i p1  +++ p2 = RStruct i (p1 +++ p2)
  RUnion i c p1 +++ p2 = RUnion i c (p1 +++ p2)
  RArray i p1   +++ p2 = RArray i (p1 +++ p2)

instance Cis c => SimpleReference (Ref c v) where
  branch Struct i p = p +++ RStruct i RHere
  branch Union i p  = p +++ RUnion noCis i RHere
  branchA i p       = p +++ RArray i RHere

class Related a where
  related :: a -> a -> Bool

instance Related (Ref c v w) where
  RHere        `related` _            = True
  _            `related` RHere        = True
  RStruct i p  `related` RStruct j q  = i == j && p `related` q
  RUnion _ i _ `related` RUnion _ j _ = i == j
  RArray i p   `related` RArray j q   = i == j && p `related` q
  _            `related` _            = False

instance FuzzyOrd Maybe (Ref c v w) where
  RHere        ==? RHere        = Just True
  RHere        ==? _            = Nothing
  _            ==? RHere        = Nothing
  RStruct i p  ==? RStruct j q  = if i == j then p ==? q else Just False
  RUnion _ i p ==? RUnion _ j q = if i == j then p ==? q else Nothing
  RArray i p   ==? RArray j q   = if i == j then p ==? q else Just False
  _            ==? _            = Nothing

  RHere        <=? RHere        = Just True
  RHere        <=? _            = Nothing
  _            <=? RHere        = Nothing
  RStruct i p  <=? RStruct j q  = if i <= j then p <=? q else Just False
  RUnion _ i p <=? RUnion _ j q = if i == j then p <=? q else Nothing
  RArray i p   <=? RArray j q   = if i <= j then p <=? q else Just False
  _            <=? _            = Nothing

rStripPrefix :: Eq c => Ref c u v -> Ref c u w -> Maybe (Ref c v w)
rStripPrefix RHere             p                 = Just p
rStripPrefix (RStruct i1 p1)   (RStruct i2 p2)   = guard (i1 == i2) >> rStripPrefix p1 p2
rStripPrefix (RUnion c1 i1 p1) (RUnion c2 i2 p2) = guard (c1 == c2 && i1 == i2) >> rStripPrefix p1 p2
rStripPrefix (RArray i1 p1)    (RArray i2 p2)    = guard (i1 == i2) >> rStripPrefix p1 p2
rStripPrefix _                 _                 = Nothing

rStripArray :: Ref c AVal w -> Maybe (Int, Ref c Val w)
rStripArray RHere        = Nothing
rStripArray (RArray i p) = Just (i, p)

follow :: (EnvReader m, Cis c) => Ref c v w -> v a -> MaybeT m (w a)
follow RHere           v                                        = return v
follow (RStruct i p)   (VStruct c _ vs)                         = do
  v <- maybeT (vs !? i)
  follow p (makeConst c v)
follow (RUnion _ i p)  (VUnion c _ (Just (i',v))) | i == i'     = follow p (makeConst c v)
follow (RUnion ci i p) (VUnion c u (Just (i',v))) | ci /= noCis = case p of
  RArray _ (RStruct j _) -> do
    cs <- cisFields u i i'
    guard (j < cs)
    follow p (makeConst c v)
  _                      -> nothingT
follow (RArray i p)    (VArray _ vs)                            = do
  v <- maybeT (vs !? i)
  follow p v
follow _               _                                        = nothingT

vUpdate :: (EnvReader m, Defined a, Cis c) => (w a -> MaybeT m (w a)) -> Ref c v w -> v a -> MaybeT m (v a)
vUpdate f RHere           v                                        = f v
vUpdate f (RStruct i p)   (VStruct c s vs)                         = do
  v <- maybeT (vs !? i)
  v' <- vUpdate f p (makeConst c v)
  return (VStruct c s (updateAt i v' vs))
vUpdate f (RUnion _ i p)  (VUnion c u (Just (i',v))) | i == i'     = do
  v' <- vUpdate f p (makeConst c v)
  return (VUnion c u (Just (i,v')))
vUpdate f (RUnion ci i p) (VUnion c u (Just (i',_))) | ci /= noCis = case p of
  RArray _ (RStruct j _) -> do
    cs <- cisFields u i i'
    guard (j < cs)
    τ <- field Union False u i
    v <- newAVal undef τ
    v' <- vUpdate f p (makeConst c v)
    return (VUnion c u (Just (i,v')))
  _                      -> nothingT
vUpdate f (RUnion _ i p)  (VUnion c u Nothing)                     = do
  τ <- field Union False u i
  v <- newAVal undef τ
  v' <- vUpdate f p (makeConst c v)
  return (VUnion c u (Just (i,v')))
vUpdate f (RArray i p)    (VArray τ vs)                            = do
  v <- maybeT (vs !? i)
  v' <- vUpdate f p v
  return (VArray τ (updateAt i v' vs))
vUpdate _ _               _                                        = nothingT

vSet :: (EnvReader m, Defined a, Cis c) => Ref c v w -> w a -> v a -> MaybeT m (v a)
vSet p w = vUpdate (\_ -> return w) p

