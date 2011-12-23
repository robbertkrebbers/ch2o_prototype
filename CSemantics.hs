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

import Debug.Trace
import Util
import Prelude
import Data.Bits
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad
import Control.Applicative
import Control.Monad.State
import Control.Monad.Maybe
import Control.Monad.Error

{- Types -}
type Id = String
data StructUnion = Struct | Union deriving (Eq, Show)
data Type = TVoid | TInt | TPointer Type | TArray Type Int | TStruct StructUnion Id deriving (Eq, Show)

instance Ord Type where
  τ1 <= τ2 | τ1 == τ2 = True
  τ1 <= TArray τ2 _   = τ1 <= τ2
  _  <= _             = False

class TypeOf a where
  typeOf :: a -> Type

isVoid :: Type -> Bool
isVoid TVoid = True
isVoid _     = False

stripPointer :: Type -> Maybe Type
stripPointer (TPointer τ) = Just τ
stripPointer _            = Nothing

isArray :: Type -> Bool
isArray (TArray _ _) = True
isArray _            = False

stripArray   :: Type -> Maybe Type
stripArray (TArray τ _) = Just τ
stripArray _            = Nothing

isInteger :: Type -> Bool
isInteger TInt = True
isInteger _    = False

isScalar :: Type -> Bool
isScalar a = isInteger a || isJust (stripPointer a)

arrayToPointer :: Type -> Type
arrayToPointer a = maybe a TPointer (stripArray a)

arrayBase :: Type -> Type
arrayBase (TArray τ _) = arrayBase τ
arrayBase τ            = τ

arrayWidth :: Type -> Int
arrayWidth (TArray τ n) = n * arrayWidth τ
arrayWidth _            = 1

{- Environments -}
type Env = Assoc (StructUnion,Id) [Type]

emptyEnv :: Env
emptyEnv = []

class (Functor m, Monad m) => EnvReader m where
  getEnv :: m Env
instance EnvReader m => EnvReader (MaybeT m) where
  getEnv = lift getEnv
instance (EnvReader m, Error e) => EnvReader (ErrorT e m) where
  getEnv = lift getEnv

fields :: StructUnion -> Id -> Env -> Maybe [Type]
fields su s e = lookup (su, s) e
fieldsDefault :: StructUnion -> Id -> Env -> [Type]
fieldsDefault su s e = fromMaybe [] (fields su s e)
field :: StructUnion -> Id -> Int -> Env -> Maybe Type
field su s x e = fields su s e >>= (!? x)
fieldM :: EnvReader m => StructUnion -> Id -> Int -> MaybeT m Type
fieldM su s x = getEnv >>= maybeT . field su s x

{- Well-formedness of types -}
isComplete :: Env -> Type -> Bool
isComplete _ TVoid          = False
isComplete _ TInt           = True
isComplete e (TPointer τ)   = isComplete e τ
isComplete e (TArray τ n)   = n >= 1 && isComplete e τ
isComplete e (TStruct su s) = (su,s) `inDom` e

checkType :: Env -> Type -> Bool
checkType _ TVoid                    = True
checkType _ TInt                     = True
checkType _ (TPointer (TStruct _ _)) = True
checkType e (TPointer τ)             = checkType e τ
checkType e (TArray τ n)             = n >= 0 && checkType e τ
checkType e (TStruct su s)           = (su,s) `inDom` e

checkTypeList :: Env -> [Type] -> Bool
checkTypeList e = all (checkType e)

checkEnv :: Env -> Bool
checkEnv []           = True
checkEnv ((sus,τs):e) = not (sus `inDom` e) && checkEnv e && checkTypeList e τs

{- Common initial segment -}
cisList :: [Type] -> [Type] -> Int
cisList (τ:τs) (σ:σs) | τ == σ = 1 + cisList τs σs
cisList _ _                    = 0

cis :: Env -> Id -> Id -> Int
cis e s1 s2 = cisList (fieldsDefault Struct s1 e) (fieldsDefault Struct s2 e)

cisFields :: Env -> Id -> Int -> Int -> Int
cisFields e u x1 x2 = fromMaybe 0 $ do
  TStruct Struct s1 <- field Union u x1 e
  TStruct Struct s2 <- field Union u x2 e
  Just (cis e s1 s2)

{- References -}
class Eq a => Related a where
  related :: a -> a -> Bool

data RefSeg = RArray Int | RStruct Int | RUnion Int Bool deriving (Eq, Show)
type Ref = [RefSeg]

refCisReset :: Ref -> Ref
refCisReset = fmap $ \r -> case r of
  RArray i   -> RArray i
  RStruct i  -> RStruct i
  RUnion i _ -> RUnion i False

target :: Env -> Ref -> Type -> Maybe Type
target _ [] τ                             = Just τ
target e (RArray i:p) τ                   = guard (0 <= i && i < arrayWidth τ) >> target e p (arrayBase τ)
target e (RStruct i:p) (TStruct Struct s) = field Struct s i e >>= target e p
target e (RUnion i _:p) (TStruct Union s) = field Union s i e >>= target e p
target _ _ _                              = Nothing

instance Related Ref where
  []             `related` _              = True
  _              `related` []             = True
  (RArray i:p)   `related` (RArray j:q)   = i == j && p `related` q
  (RStruct i:p)  `related` (RStruct j:q)  = i == j && p `related` q
  (RUnion i _:_) `related` (RUnion j _:_) = i == j
  _              `related` _              = False

instance FuzzyOrd Maybe Ref where
  []           ==? []           = Just True
  []           ==? _            = Nothing
  _            ==? []           = Nothing
  RArray i:p   ==? RArray j:q   = if i == j then p ==? q else Just False
  RStruct i:p  ==? RStruct j:q  = if i == j then p ==? q else Just False
  RUnion i _:p ==? RUnion j _:q = if i == j then p ==? q else Nothing
  _            ==? _            = Nothing

  []           <=? []           = Just True
  []           <=? _            = Nothing
  _            <=? []           = Nothing
  RArray i:p   <=? RArray j:q   = if i <= j then p <=? q else Just False
  RStruct i:p  <=? RStruct j:q  = if i <= j then p <=? q else Just False
  RUnion i _:p <=? RUnion j _:q = if i == j then p <=? q else Nothing
  _            <=? _            = Nothing

{- Blocks -}
type Block = Int

class BlockOf a where
  blockOf :: a -> Block

{- Addresses -}
data Addr = Addr {
  aBlock :: Block,
  aRef :: Ref,   -- (last aRef) should not be an RArray
  aType :: Type, -- the target type of aRef (that is not the type the address points to)
  aOffset :: Int -- an offset into aRef (this is a delayed RArray that is allowed to be one past)
} deriving (Eq, Show)

instance BlockOf Addr where
  blockOf = aBlock

addr :: Block -> Type -> Addr
addr b τ = Addr b [] τ 0

aMap :: (Block -> Maybe Block) -> Addr -> Maybe Addr
aMap f (Addr a p τ i) = do b <- f a; Just (Addr b p τ i)

aLength :: Addr -> Int
aLength = arrayWidth . aType

aInRange :: Addr -> Bool
aInRange a = aOffset a < aLength a

instance TypeOf Addr where
  typeOf = arrayBase . aType

move :: Int -> Addr -> Maybe Addr
move x a = do
  guard (0 <= aOffset a + x && aOffset a + x <= aLength a)
  Just a { aOffset = aOffset a + x }

aMinus :: Type -> Addr -> Addr -> Maybe Int
aMinus τ (Addr a1 p1 _ i1) (Addr a2 p2 _ i2) = do
  guard (a1 == a2 && p1 == p2) -- if well-formed, the types are equal
  let n = i1 - i2 in do
  guard (n `rem` arrayWidth τ == 0)
  return (n `quot` arrayWidth τ)

normalizedRef :: Addr -> Maybe Ref
normalizedRef (Addr _ p τ i) = do
  guard (0 <= i && i < arrayWidth τ)
  Just (p ++ [RArray i])

checkAddr' :: Env -> (Block -> Maybe Type) -> Addr -> Bool
checkAddr' e t (Addr a p τ i) = 0 <= i && i < arrayWidth τ &&
                    (t a >>= target e p) == Just τ

aCisReset :: Addr -> Addr
aCisReset a = a { aRef = refCisReset (aRef a) }

{- Values -}
data Val = VUndef Type | VInt Integer | VNULL Type | VPointer Type Addr |
  VStruct Id [AVal] | VUnion Id (Maybe (Int,AVal)) deriving (Eq, Show)
data AVal = VArray Type [Val] deriving (Eq, Show)

zeroVal :: Type -> Val
zeroVal TInt         = VInt 0
zeroVal (TPointer τ) = VNULL τ
zeroVal τ            = VUndef τ

vMap :: (Addr -> Maybe Addr) -> Val -> Val
vMap _ (VUndef τ)     = VUndef τ
vMap _ (VInt x)       = VInt x
vMap _ (VNULL τ)      = VNULL τ
vMap f (VPointer τ a) = case f a of
  Nothing -> VUndef (TPointer τ)
  Just b  -> VPointer τ b
vMap f (VStruct s vs) = VStruct s (aVMap f <$> vs)
vMap f (VUnion s v')  = VUnion s (mapSnd (aVMap f) <$> v')

aVMap :: (Addr -> Maybe Addr) -> AVal -> AVal
aVMap f (VArray τ vs)  = VArray τ (vMap f <$> vs)

{- Typing of values -}
instance TypeOf Val where
  typeOf (VUndef τ)     = τ
  typeOf (VInt _)       = TInt
  typeOf (VNULL τ)      = TPointer τ
  typeOf (VPointer τ _) = TPointer τ
  typeOf (VStruct s _)  = TStruct Struct s
  typeOf (VUnion s _)   = TStruct Union s

instance TypeOf AVal where
  typeOf (VArray τ _)   = τ

isDef :: Val -> Bool
isDef (VUndef _) = False
isDef _          = True

aVal :: Val -> AVal
aVal v = VArray (typeOf v) [v]

checkVal' :: Env -> (Block -> Maybe Type) -> Val -> Bool
checkVal' e _ (VUndef τ)             = checkType e τ
checkVal' _ _ (VInt _)               = True
checkVal' e _ (VNULL τ)              = checkType e τ
checkVal' e t (VPointer τ a)         = case t (aBlock a) of
  Just σ  -> checkAddr' e t a && τ < σ
  Nothing -> False
checkVal' e t (VStruct s vs)         = maybe False (checkAValList' e t vs) (fields Struct s e)
checkVal' e _ (VUnion s Nothing)     = (Union,s) `inDom` e
checkVal' e t (VUnion s (Just(i,v))) = field Union s i e == Just (typeOf v) && checkAVal' e t v

checkAVal' :: Env -> (Block -> Maybe Type) -> AVal -> Bool
checkAVal' e t (VArray τ vs) = length vs == arrayWidth τ &&
                                all (\v -> typeOf v == arrayBase τ && checkVal' e t v) vs

checkAValList' :: Env -> (Block -> Maybe Type) -> [AVal] -> [Type] -> Bool
checkAValList' _ _ [] []         = True
checkAValList' e t (v:vs) (τ:τs) = typeOf v == τ && checkAVal' e t v && checkAValList' e t vs τs
checkAValList' _ _ _ _           = False

{- Manipulation of values -}
cast :: EnvReader m => Val -> Type -> MaybeT m Val
cast (VPointer _ a) (TPointer TVoid) = return (VPointer TVoid a)
-- a weaker alternative would be:
--   cast (VPointer _ a) (TPointer τ) = guard (arrayBase τ == typeOf a) >> return (VPointer τ a)
cast (VPointer _ a) (TPointer τ)     = guard (τ < aType a) >> return (VPointer τ a)
cast (VNULL _)      (TPointer τ)     = return (VNULL τ)
cast v              τ                = guard (typeOf v == τ) >> return v

follow :: Env -> Ref -> Val -> Maybe Val
follow _ [] τ                                              = Just τ
follow e (RStruct i:p) (VStruct _ vs)                      = vs !? i >>= followA e p
follow e (RUnion i _:p) (VUnion _ (Just (i',v))) | i == i' = followA e p v
follow e (RUnion i True:p) (VUnion u (Just (i',v)))        =
  case p of
    RArray _:RStruct j:_ -> guard (j < cisFields e u i i') >> followA e p v
    _                    -> Nothing
follow _ _ _                                               = Nothing

followA :: Env -> Ref -> AVal -> Maybe Val
followA e (RArray i:p) (VArray _ vs) = vs !? i >>= follow e p
followA _ _ _                        = Nothing

followAM :: EnvReader m => Ref -> AVal -> MaybeT m Val
followAM r v = do e <- getEnv; maybeT (followA e r v)

newVal :: (Type -> Val) -> Env -> Type -> Val
newVal f e (TStruct Struct s) = VStruct s (newAVal f e <$> fieldsDefault Struct s e)
newVal _ _ (TStruct Union s)  = VUnion s Nothing
newVal f _ τ                  = f τ

newAVal :: (Type -> Val) -> Env -> Type -> AVal
newAVal f e τ = VArray τ (replicate (arrayWidth τ) (newVal f e (arrayBase τ)))

set :: Env -> Val -> Ref -> Val -> Maybe Val
set _ w [] _                                              = Just w
set e w (RStruct i:p) (VStruct s vs)                      = do
  v' <- vs !? i >>= setA e w p
  Just (VStruct s (updateAt i v' vs))
set e w (RUnion i _:p) (VUnion s (Just (i',v))) | i == i' = do
  guard (i == i')
  v' <- setA e w p v
  Just (VUnion s (Just (i,v')))
set e w (RUnion i _:p) (VUnion s _)                       = do
  τ <- field Union s i e
  v' <- setA e w p (newAVal VUndef e τ)
  Just (VUnion s (Just (i,v')))
set _ _ _ _                                               = Nothing

setA :: Env -> Val -> Ref -> AVal -> Maybe AVal
setA e w (RArray i:p) (VArray τ vs) = do
  v' <- vs !? i >>= set e w p
  Just (VArray τ (updateAt i v' vs))
setA _ _ _             _            = Nothing

{- L-values -}
data LVal = LVal Type Addr deriving (Eq, Show)

lVal :: Addr -> LVal
lVal a = LVal (aType a) a

instance TypeOf LVal where
  typeOf (LVal τ _) = τ

{- Memory -}
data MemFlag = MStatic | MAuto | MTemp | MMalloc deriving (Eq, Show)

data Cell = Cell { cVal :: AVal, cFlag :: MemFlag } deriving (Eq, Show)

instance TypeOf Cell where
  typeOf = typeOf . cVal

cMap :: (AVal -> AVal) -> Cell -> Cell
cMap f (Cell v fl) = Cell (f v) fl

data Mem = Mem { memEnv :: Env, blocks :: Map Block Cell, nextBlock :: Block }
  deriving (Eq, Show)

class (Functor m, Monad m) => MemReader m where
  getMem :: m Mem
class MemReader m => MemWriter m where
  setMem :: Mem -> m ()
instance MemReader (State Mem) where
  getMem = get
instance MemReader m => MemReader (MaybeT m) where
  getMem = lift getMem
instance MemWriter m => MemWriter (MaybeT m) where
  setMem m = lift (setMem m)
instance (MemReader m, Error e) => MemReader (ErrorT e m) where
  getMem = lift getMem
instance (MemWriter m, Error e) => MemWriter (ErrorT e m) where
  setMem m = lift (setMem m)
instance MemReader m => EnvReader m where
  getEnv = fmap memEnv getMem

emptyMem :: Mem
emptyMem = Mem emptyEnv Map.empty 0

modifyMem :: MemWriter m => (Mem -> Mem) -> m ()
modifyMem f = getMem >>= setMem . f

getCell :: MemReader m => Block -> MaybeT m Cell
getCell b = getMem >>= maybeT . Map.lookup b . blocks

blockValid :: MemReader m => Block -> m Bool
blockValid b = getMem >>= return . Map.member b . blocks

isDeterminate :: MemReader m => Val -> m Bool
isDeterminate (VPointer _ a) = blockValid (aBlock a)
isDeterminate v              = return (isDef v)

flagOfBlock :: MemReader m => Block -> MaybeT m MemFlag
flagOfBlock b = cFlag <$> getCell b

typeOfBlock :: MemReader m => Block -> MaybeT m Type
typeOfBlock b = typeOf <$> getCell b

blockLVal :: MemReader m => Block -> MaybeT m LVal
blockLVal b = lVal . addr b <$> typeOfBlock b

typeOfBlock' :: Block -> Mem -> Maybe Type
typeOfBlock' b m = typeOf <$> Map.lookup b (blocks m)

checkAddr :: Mem -> Addr -> Bool
checkAddr m = checkAddr' (memEnv m) (flip typeOfBlock' m)

checkMVal :: Mem -> Val -> Bool
checkMVal m = checkVal' (memEnv m) (flip typeOfBlock' m)

checkAVal :: Mem -> AVal -> Bool
checkAVal m = checkAVal' (memEnv m) (flip typeOfBlock' m)

aBranch :: MemReader m => StructUnion -> Int -> Addr -> MaybeT m Addr
aBranch su i a = case typeOf a of
  TStruct su' s -> do
    guardM (blockValid (aBlock a))
    guard (su' == su)
    τ <- fieldM su s i
    p <- maybeT (normalizedRef a)
    return (Addr (aBlock a) (p ++ [r]) τ 0)
  _             -> nothingT
 where
  r = case su of Struct -> RStruct i; Union -> RUnion i True

instance Related Addr where
  Addr a1 p1 _ i1 `related` Addr a2 p2 _ i2 = a1 == a2 &&  p1 `related` p2 && i1 == i2

instance MemReader m => FuzzyOrd (MaybeT m) Addr where
  a ==? b | aBlock a == aBlock b = do
    guardM (blockValid (aBlock a))
    r <- maybeT (aRef a ==? aRef b)
    if r
    then return (aOffset a == aOffset b)
    else guard (aInRange a && aInRange b) >> return False
  a ==? b | otherwise            = do
    fa <- flagOfBlock (aBlock a)
    fb <- flagOfBlock (aBlock b)
    guard (fa /= MTemp && fb /= MTemp && aInRange a && aInRange b)
    return False

  a <=? b | aBlock a == aBlock b = do
    guardM (blockValid (aBlock a))
    r <- maybeT (aRef a ==? aRef b)
    if r
    then return (aOffset a <= aOffset b)
    else guard (aInRange a && aInRange b) >> maybeT (aRef a <=? aRef b)
  _ <=? _ | otherwise            = nothingT

allocArray :: MemWriter m => AVal -> MemFlag -> m Block
allocArray v f = do
  Mem e bs n <- getMem
  setMem (Mem e (Map.insert n (Cell v' f) bs) (n+1))
  return n
 where
  v' = aVMap (Just . aCisReset) v

alloc :: MemWriter m => Type -> Maybe AVal -> MemFlag -> m Block
alloc _ (Just v) f = allocArray v f
alloc τ Nothing  f = do
  e <- getEnv --  guard (checkType e τ)
  allocArray (newAVal fi e τ) f
 where fi = if f == MStatic then zeroVal else VUndef

{-
cleanAddr :: (Block -> Bool) -> Addr -> Maybe Addr
cleanAddr f = aMap $ \b -> if f b then Nothing else Just b

cleanVal :: (Block -> Bool) -> Val -> Val
cleanVal f = vMap (cleanAddr f)

cleanAVal :: (Block -> Bool) -> AVal -> AVal
cleanAVal f = aVMap (cleanAddr f)
-}

freeUnchecked :: MemWriter m => Block -> m ()
freeUnchecked b = modifyMem $ \m -> m { blocks = Map.delete b (blocks m) }

free :: MemWriter m => Block -> MaybeT m ()
free b = do
  MMalloc <- flagOfBlock b
  lift (freeUnchecked b)

load :: MemReader m => Block -> Ref -> MaybeT m Val
load b p = do
  e <- getEnv
  Cell v _ <- getCell b
  v' <- maybeT (followA e p v)
  guardM (isDeterminate v')
  return v'

loadA :: MemReader m => Addr -> MaybeT m Val
loadA a = do p <- maybeT (normalizedRef a); load (aBlock a) p

store :: MemWriter m => Block -> Ref -> Val -> MaybeT m ()
store b p w = do
  e <- getEnv
  Cell v f <- getCell b
  guard (f /= MTemp)
--  guard (target e p (typeOf v) == Just (typeOf w)) -- hmm, what to check here?
  v' <- maybeT (setA e w' p v)
  modifyMem $ \m -> m { blocks = Map.insert b (Cell v' f) (blocks m) }
 where
  w' = vMap (Just . aCisReset) w

storeA :: MemWriter m => Addr -> Val -> MaybeT m ()
storeA a v = do p <- maybeT (normalizedRef a); store (aBlock a) p v

aToVal :: MemWriter m => AVal -> MaybeT m (Maybe Block, Val)
aToVal ar@(VArray (TArray τ n) _) = do
  b <- allocArray ar MTemp
  return (Just b, VPointer τ (addr b (TArray τ n)))
aToVal (VArray _ [v])             = guardM (isDeterminate v) >> return (Nothing, v)
aToVal (VArray _ _)               = nothingT

{- Operations -}
data BinOp = PlusOp | MinusOp | MultOp | DivOp | RemOp | ShiftLOp | ShiftROp |
  LeOp | LtOp | GeOp | GtOp | EqOp | NeOp |
  BitAndOp | BitOrOp | BitXorOp deriving (Eq, Show)
data UnOp = NotOp | CompOp | NegOp deriving (Eq, Show)

boolToInt :: Bool -> Integer
boolToInt b = if b then 1 else 0

intToBool :: Integer -> Bool
intToBool = (0 /=)

boolToVal :: Bool -> Val
boolToVal = VInt . boolToInt

vFalse :: Val
vFalse = boolToVal False

vTrue :: Val
vTrue = boolToVal True

valToBool :: Val -> Maybe Bool
valToBool (VInt x)       = Just (intToBool x)
valToBool (VNULL _)      = Just False
valToBool (VPointer _ _) = Just True
valToBool _              = Nothing

negateVal :: Val -> Maybe Val
negateVal v = boolToVal <$> not <$> valToBool v

evalUnOpInt :: UnOp -> Integer -> Maybe Integer
evalUnOpInt CompOp x = Just (complement x)
evalUnOpInt NegOp  x = Just (negate x)
evalUnOpInt NotOp  x = Just (boolToInt (not (intToBool x)))

evalUnOp :: MemReader m => UnOp -> Val -> MaybeT m Val
evalUnOp op    (VInt x) = maybeT (VInt <$> evalUnOpInt op x)
evalUnOp NotOp v        = maybeT (negateVal v)
evalUnOp _ _            = nothingT

typeBinOp :: BinOp -> Type -> Type -> Maybe Type
typeBinOp NeOp    τ1            τ2            = typeBinOp EqOp τ1 τ2
typeBinOp GeOp    τ1            τ2            = typeBinOp LeOp τ2 τ1
typeBinOp GtOp    τ1            τ2            = typeBinOp LtOp τ2 τ1
typeBinOp _       TInt          TInt          = Just TInt
typeBinOp PlusOp  (TPointer τ)  TInt          = Just (TPointer τ)
typeBinOp PlusOp  TInt          (TPointer τ)  = Just (TPointer τ)
typeBinOp MinusOp (TPointer τ1) (TPointer τ2) = guard (τ1 == τ2) >> Just TInt
typeBinOp EqOp    (TPointer τ1) (TPointer τ2) = guard (τ1 == τ2) >> Just (TPointer τ1)
typeBinOp LeOp    (TPointer τ1) (TPointer τ2) = guard (τ1 == τ2) >> Just (TPointer τ1)
typeBinOp LtOp    (TPointer τ1) (TPointer τ2) = guard (τ1 == τ2) >> Just (TPointer τ1)
typeBinOp _       _             _             = Nothing

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

evalBinOp :: MemReader m => BinOp -> Val -> Val-> MaybeT m Val
evalBinOp op      (VInt x)         (VInt y)         = maybeT (VInt <$> evalBinOpInt op x y)
evalBinOp NeOp    v1               v2               = evalBinOp EqOp v1 v2 >>= maybeT . negateVal
evalBinOp GeOp    v1               v2               = evalBinOp LeOp v2 v1
evalBinOp GtOp    v1               v2               = evalBinOp LtOp v2 v1
evalBinOp PlusOp  (VInt x)         (VPointer τ a)   = maybeT (VPointer τ <$> move (fromEnum x * arrayWidth τ) a)
evalBinOp PlusOp  (VPointer τ a)   (VInt x)         = maybeT (VPointer τ <$> move (fromEnum x * arrayWidth τ) a)
evalBinOp MinusOp (VPointer τ1 a1) (VPointer τ2 a2) = guard (τ1 == τ2) >> maybeT (VInt <$> toEnum <$> aMinus τ1 a1 a2)
evalBinOp MinusOp (VNULL τ1)       (VNULL τ2)       = guard (τ1 == τ2) >> return (VInt 0)
evalBinOp EqOp    (VPointer τ1 _)  (VNULL τ2)       = guard (τ1 == τ2) >> return vFalse
evalBinOp EqOp    (VNULL τ1)       (VPointer τ2 _)  = guard (τ1 == τ2) >> return vFalse
evalBinOp EqOp    (VPointer τ1 a1) (VPointer τ2 a2) = guard (τ1 == τ2) >> boolToVal <$> (a1 ==? a2)
evalBinOp EqOp    (VNULL τ1)       (VNULL τ2)       = guard (τ1 == τ2) >> return vTrue
evalBinOp LeOp    (VPointer τ1 a1) (VPointer τ2 a2) = guard (τ1 == τ2) >> boolToVal <$> (a1 <=? a2)
evalBinOp LeOp    (VNULL τ1)       (VNULL τ2)       = guard (τ1 == τ2) >> return vTrue
evalBinOp LtOp    (VPointer τ1 a1) (VPointer τ2 a2) = guard (τ1 == τ2) >> boolToVal <$> (a1 <? a2)
evalBinOp LtOp    (VNULL τ1)       (VNULL τ2)       = guard (τ1 == τ2) >> return vFalse
evalBinOp _       _                _                = nothingT

{- Expressions -}
data Expr :: * -> * where
  -- type expressions
  VLType    :: Type -> VLType
  VLPointer :: VLType -> VLType
  VLArray   :: VLType -> RExpr -> VLType
  -- right expressions
  EVal      :: Val -> RExpr
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
type RExpr  = Expr Val
type LExpr  = Expr LVal

deriving instance Eq (Expr a)
deriving instance Show (Expr a)

eMap :: (Type -> Type) -> (Val -> Val) -> (LVal -> LVal) -> Expr a -> Expr a
eMap ft fv fl = m
 where
  m :: Expr a -> Expr a
  m (VLType τ)        = VLType (ft τ)
  m (VLPointer τ)     = VLPointer (m τ)
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
constExpr f (VLPointer τ)     = TPointer <$> constExpr f τ
constExpr f (VLArray τvl r)   = do
  τ <- constExpr f τvl
  VInt n <- constExpr f r
  guard (n >= 1)
  return (TArray τ (fromEnum n))
constExpr _ (EVal a)          = return a
constExpr f (EToVal l)        = do
  LVal (TArray τ _) a <- constExpr f l
  return (VPointer τ a)
constExpr f (EAddrOf l)       = do
  LVal τ a <- constExpr f l
  return (VPointer τ a)
constExpr f (EBinOp op r1 r2) = do
  v1 <- constExpr f r1
  v2 <- constExpr f r2
  evalBinOp op v1 v2
constExpr f (EUnOp op r)      = do
  v <- constExpr f r
  evalUnOp op v
constExpr f (EIf r1 r2 r3)    = do
  b <- constExpr f r1 >>= maybeT . valToBool
  if b then constExpr f r2 else constExpr f r3
constExpr f (ECast τvl r)     = do
  τ <- constExpr f τvl
  v <- constExpr f r
  cast v τ
constExpr _ (ELVal a)         = return a
constExpr f (EVar x)          = f x >>= blockLVal
constExpr f (EDeref r)        = do
  VPointer τ a <- constExpr f r
  guard (not (isVoid τ) && aInRange a)
  return (LVal τ a)
constExpr f (ELField su i l)  = do
  LVal _ a <- constExpr f l
  a' <- aBranch su i a
  return (lVal a')
constExpr _ _                 = nothingT

constExpr_ :: Expr a -> Maybe a
constExpr_ e = evalState (runMaybeT (constExpr (\_ -> nothingT) e)) emptyMem

eTrue :: RExpr
eTrue = EVal vTrue

eFalse :: RExpr
eFalse = EVal vFalse

eAnd :: RExpr -> RExpr -> RExpr
eAnd r1 r2 = EIf r1 (EIf r2 eTrue eFalse) eFalse

eOr :: RExpr -> RExpr -> RExpr
eOr r1 r2 = EIf r1 eTrue (EIf r2 eTrue eFalse)

vlErase :: VLType -> Type
vlErase (VLType τ)    = τ
vlErase (VLPointer τ) = TPointer (vlErase τ)
vlErase (VLArray τ r) = case constExpr_ r of
  Just (VInt n) -> TArray (vlErase τ) (fromEnum n)
  _             -> TArray (vlErase τ) 0

{-
cleanExpr :: (Block -> Bool) -> Expr a -> Expr a
cleanExpr f = eMap id (cleanVal f) (lMap (cleanAddr f))
-}

{- Expression contexts -}
data ECtx :: * -> * -> * where
  CtxTop     :: ECtx b b
  -- for types
  CtxPointer :: TCtx b -> TCtx b
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
type RCtx = ECtx Val
type LCtx = ECtx LVal

deriving instance Eq (ECtx a b)
deriving instance Show (ECtx a b)

eCtxMap :: (VLType -> VLType) -> (RExpr -> RExpr) -> (LExpr -> LExpr) -> ECtx a b -> ECtx a b
eCtxMap ft fr fl = m
 where
  m :: ECtx a b -> ECtx a b
  m CtxTop                = CtxTop
  m (CtxPointer k)        = CtxPointer (m k)
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

{- 
cleanECtx :: (Block -> Bool) -> ECtx a b -> ECtx a b
cleanECtx f = eCtxMap (cleanExpr f) (cleanExpr f) (cleanExpr f)
-}

class Subst a b c | a b -> c where
  subst :: a -> b -> c

instance Subst (ECtx a b) (Expr a) (Expr b) where
  subst CtxTop                b  = b
  subst (CtxPointer k)        τ  = subst k (VLPointer τ)
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
  RedArray    :: TCtx b -> Type -> Val -> Redex b
  RedCall     :: RCtx b -> Id -> [Val] -> Redex b
  RedAssign   :: RCtx b -> LVal -> Val -> Redex b
  RedToVal    :: RCtx b -> LVal -> Redex b
  RedAddrOf   :: RCtx b -> LVal -> Redex b
  RedFieldCis :: RCtx b -> Int -> Int -> Val -> Redex b
  RedField    :: RCtx b -> StructUnion -> Int -> Val -> Redex b
  RedBinOp    :: RCtx b -> BinOp -> Val -> Val -> Redex b
  RedUnOp     :: RCtx b -> UnOp -> Val -> Redex b
  RedPreOp    :: RCtx b -> BinOp -> LVal -> Val -> Redex b
  RedPostOp   :: RCtx b -> BinOp -> LVal -> Val -> Redex b
  RedCast     :: RCtx b -> Type -> Val -> Redex b
  RedIf       :: RCtx b -> Val -> RExpr -> RExpr -> Redex b
  RedComma    :: RCtx b -> Val -> RExpr -> Redex b
  RedVar      :: LCtx b -> Id -> Redex b
  RedDeref    :: LCtx b -> Val -> Redex b
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
  split' _ (VLType τ)          = Left τ
  split' k (VLPointer τ)     = case split' (CtxPointer k) τ of
    Left σ    -> Right [RedPointer k σ]
    Right rds -> Right rds
  split' k (VLArray τ r)     = case (split' (CtxArrayL r k) τ, split' (CtxArrayR τ k) r) of
    (Left σ,     Left v)     -> Right [RedArray k σ v]
    (Right rds,  Left _)     -> Right rds
    (Left _,     Right rds)  -> Right rds
    (Right rds1, Right rds2) -> Right (rds1 ++ rds2)
  split' _ (EVal v)          = Left v
  split' k (ECall x rs)      = case split'Args [] rs of
    Left vs   -> Right [RedCall k x vs]
    Right rds -> Right rds
   where
    split'Args _   []      = Left []
    split'Args rsr (r:rsl) = case (split' (CtxCall x rsr rsl k) r, split'Args (r:rsr) rsl) of
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

{- Declarations -}
data Decl = DAuto Type | DStatic Block deriving (Eq, Show)
data AllocDecl = AllocAuto Block | AllocStatic Block deriving (Eq, Show)

allocD :: MemWriter m => Decl -> MaybeT m AllocDecl
allocD (DAuto τ)   = alloc τ Nothing MAuto >>= return . AllocAuto
allocD (DStatic b) = return (AllocStatic b)

freeD :: MemWriter m => AllocDecl -> MaybeT m Decl
freeD (AllocAuto b)   = do
  τ <- typeOfBlock b
  freeUnchecked b
  return (DAuto τ)
freeD (AllocStatic b) = return (DStatic b)

instance BlockOf AllocDecl where
  blockOf (AllocAuto b)   = b
  blockOf (AllocStatic b) = b

{- Statements -}
data Trap = Continue | Break deriving (Eq, Show)

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
  deriving (Eq, Show)

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
  deriving (Eq, Show)

type SCtx = [SCtxSeg]
type SInCtx = (SCtx,Stmt)

getLocal :: Id -> SCtx -> Maybe Block
getLocal _ []                   = Nothing
getLocal x (CtxBlock ds:k)      = (blockOf <$> lookup x ds) `mplus` getLocal x k
getLocal x (CtxVLDecl x' _ b:k) = if x == x' then Just b else getLocal x k
getLocal x (_:k)                = getLocal x k

data PathSeg = Up | Down Int deriving (Eq, Show)
type Path = [PathSeg]

changeCtx :: MemWriter m => Path -> SInCtx -> MaybeT m SInCtx
changeCtx [] sc                         = return sc
changeCtx (Up:p) (CtxBlock ds:k, s)     = do
  fds <- mapMAssoc freeD ds
  changeCtx p (k, SBlock fds s)
changeCtx (Up:p) (CtxVLDecl x τ b:k, s) = freeUnchecked b >> changeCtx p (k, SVLDecl x τ s)
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
  ads <- mapMAssoc allocD ds
  changeCtx p (CtxBlock ads:k, s)
changeCtx (Down 0:_) (_, SVLDecl _ _ _) = nothingT --jumping into a VLA block is undefined
changeCtx (Down 0:p) (k, SComp s1 s2)   = changeCtx p (CtxCompL s2:k, s1)
changeCtx (Down 1:p) (k, SComp s1 s2)   = changeCtx p (CtxCompR s1:k, s2)
changeCtx (Down 0:p) (k, SIf e st sf)   = changeCtx p (CtxIfT e sf:k, st)
changeCtx (Down 1:p) (k, SIf e st sf)   = changeCtx p (CtxIfF e st:k, sf)
changeCtx (Down 0:p) (k, SSwitch e s)   = changeCtx p (CtxSwitch e:k, s)
changeCtx (Down 0:p) (k, SLabel l s)    = changeCtx p (CtxLabel l:k, s)
changeCtx (Down 0:p) (k, SCase c s)     = changeCtx p (CtxCase c:k, s)
changeCtx (Down 0:p) (k, SLoop s)       = changeCtx p (CtxLoop:k, s)
changeCtx (Down 0:p) (k, SSetTrap t s)  = changeCtx p (CtxSetTrap t:k, s)
changeCtx _          _                  = nothingT

next :: MemWriter m => SInCtx -> MaybeT m (Maybe SInCtx)
next (k',s') = case next' k' of
  Just p  -> Just <$> changeCtx p (k',s')
  Nothing -> return Nothing
 where
  next' :: SCtx -> Maybe Path
  next' []             = Nothing
  next' (CtxCompL _:_) = Just [Up,Down 1]
  next' (CtxLoop:_)    = Just []
  next' (_:k)          = (Up:) <$> next' k

toTrap :: MemWriter m => Trap -> SInCtx -> MaybeT m SInCtx
toTrap t (k',s') = do
  p <- maybeT (toTrap' k')
  changeCtx p (k',s')
 where
  toTrap' :: SCtx -> Maybe Path
  toTrap' []                = Nothing
  toTrap' (CtxSetTrap t':k) = if t == t' then Just [] else (Up:) <$> toTrap' k
  toTrap' (_:k)             = (Up:) <$> toTrap' k

toLabel :: MemWriter m => Id -> SInCtx -> MaybeT m SInCtx
toLabel l (k',s') = do
  p <- maybeT (down s' `mplus` up k')
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

toCase :: MemWriter m => Integer -> SInCtx -> MaybeT m SInCtx
toCase c (k',s') = do
  p <- maybeT (toCase' (Just c) s' `mplus` toCase' Nothing s')
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

toTop :: MemWriter m => SInCtx -> MaybeT m SInCtx
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
type RInS = EInS Val

deriving instance Eq b   => Eq (EInS b)
deriving instance Show b => Show (EInS b)

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
  eExpr :: Expr b,
  eTmps :: [Block]
} deriving (Eq, Show)

ctxVLDeclT :: SCtx -> Id -> VLType -> Stmt -> EInSCtx Type
ctxVLDeclT k x τ s = EInSCtx k (CtxVLDeclT x s) τ []

ctxExpr :: SCtx -> RExpr -> EInSCtx Val
ctxExpr k r = EInSCtx k CtxExpr r []

ctxReturn :: SCtx -> RExpr -> EInSCtx Val
ctxReturn k r = EInSCtx k CtxReturn r []

ctxIfE :: SCtx -> RExpr -> Stmt -> Stmt -> EInSCtx Val
ctxIfE k r st sf = EInSCtx k (CtxIfE st sf) r []

ctxSwitchE :: SCtx -> RExpr -> Stmt -> EInSCtx Val
ctxSwitchE k r s = EInSCtx k (CtxSwitchE s) r []

{- States -}
data Fun = Fun {
  funArgs :: Assoc Id Type,
  funType :: Type,
  funStmt :: Stmt
} deriving (Eq, Show)

data Return = forall b . Return (EInSCtx b) (RCtx b)

{-
cleanReturn :: (Block -> Bool) -> Return -> Return
cleanReturn f (Return es k) = Return es (cleanECtx f k)
-}

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

instance MemReader CMonad where
  getMem = gets stateMem
instance MemWriter CMonad where
  setMem m = modify $ \s -> s { stateMem = m }

getGlobal :: Id -> CMaybe Block
getGlobal x = gets stateGlobals >>= maybeT . Map.lookup x

getVar :: Id -> SCtx -> CMaybe Block
getVar x ek = maybeT (getLocal x ek) `mplus` getGlobal x

varLVal :: Id -> SCtx -> CMaybe LVal
varLVal x k = getVar x k >>= blockLVal

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

instantiate :: MemWriter m => Fun -> [Val] -> MaybeT m SInCtx
instantiate (Fun xs _ s) vs = do
  guard (length xs == length vs)
  guardM (allM isDeterminate vs)
  ads <- mapMAssoc f (zipWith (\(x,_) rv -> (x,rv)) xs vs)
  return ([CtxBlock ads], s)
 where
  f :: MemWriter m => Val -> MaybeT m AllocDecl
  f v = AllocAuto <$> allocArray (aVal v) MAuto

{- Evaluation -}
data E =
  ES SInCtx | -- evaluating a statement
  forall b . EE (EInSCtx b) (Expr b) | -- evaluating an expression
  EF Val -- and ... we're done!

instance Show E where
  show (ES sk)   = show sk
  show (EE es b) = case eInS es of _ -> show (subst (eInS es) b)
  show (EF v)    = show v

nextExpr :: EInSCtx b -> ECtx a b -> Expr a -> CMaybe E
nextExpr es k a = return (EE es (subst k a))

nextExprA :: EInSCtx b -> RCtx b -> AVal -> CMaybe E
nextExprA es k ar = do
  (mb,v) <- aToVal ar
  case mb of
    Nothing -> nextExpr es k (EVal v)
    Just b  -> nextExpr (es { eTmps = b:eTmps es }) k (EVal v)

funReturn :: Val -> SInCtx -> CMaybe E
funReturn v sk = do
  _ <- toTop sk -- free all declarations
  guardM (isDeterminate v)
  mr <- lift popReturn
  case mr of
    Nothing            -> return (EF v)
    Just (Return es k) -> nextExpr es k (EVal v)

nextStmt :: SInCtx -> CMaybe E
nextStmt sk = next sk >>= maybe (funReturn (VUndef TVoid) sk) (return . ES)

{- Evaluation of statements -}
stmtStep :: SInCtx -> CMaybe E
stmtStep (k, SBlock ds s)        = do
  ads <- mapMAssoc allocD ds
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
stmtStep sk@(_, SReturn Nothing) = funReturn (VUndef TVoid) sk
stmtStep (k, SComp sl sr)        = return (ES (CtxCompL sr:k, sl))
stmtStep sk@(_, SSkip)           = nextStmt sk

{- Evaluation of expressions -}
redexStep :: EInSCtx b -> Redex b -> CMaybe E
redexStep es (RedPointer k τ)               = nextExpr es k (VLType (TPointer τ))
redexStep es (RedArray k τ v)               = case v of
  VInt n | n >= 1 -> nextExpr es k (VLType (TArray τ (fromEnum n)))
  _               -> nothingT
redexStep es (RedCall k x vs)               = do
  f <- getFun x
  lift (pushReturn (Return es k))
  ES <$> instantiate f vs
redexStep es (RedAssign k (LVal _ a) v)     = do
  storeA a v -- fails if a is indeterminate
  nextExpr es k (EVal v)
redexStep es (RedToVal k (LVal τ a))        = do
  case τ of
   TArray σ _ -> guardM (blockValid (aBlock a)) >> nextExpr es k (EVal (VPointer σ a))
   _          -> loadA a >>= nextExpr es k . EVal -- fails if a is indeterminate
redexStep es (RedAddrOf k (LVal τ a))       = do
  guardM (blockValid (aBlock a))
  nextExpr es k (EVal (VPointer τ a))
redexStep es (RedFieldCis k i j' v)         = case v of
  VUnion u (Just (j,VArray _ [VStruct _ vs])) -> do
    e <- getEnv
    guard (i <= cisFields e u j j')
    maybeT (vs !? i) >>= nextExprA es k
  _                                           -> nothingT
redexStep es (RedField k Struct i v)        = case v of
  VStruct _ vs -> maybeT (vs !? i) >>= nextExprA es k
  _            -> nothingT
redexStep es (RedField k Union j v)         = case v of
  VUnion _ (Just (j',v')) | j' == j -> nextExprA es k v'
  _                                 -> nothingT
redexStep es (RedBinOp k op v1 v2)          = do
  guardM (isDeterminate v1)
  guardM (isDeterminate v2)
  evalBinOp op v1 v2 >>= nextExpr es k . EVal
redexStep es (RedUnOp k op v)               = evalUnOp op v >>= nextExpr es k . EVal
redexStep es (RedPreOp k op (LVal _ a) v2)  = do
  v1 <- loadA a -- fails if a is indeterminate
  guardM (isDeterminate v2)
  v <- evalBinOp op v1 v2
  storeA a v
  nextExpr es k (EVal v)
redexStep es (RedPostOp k op (LVal _ a) v2) = do
  v1 <- loadA a -- fails if a is indeterminate
  guardM (isDeterminate v2)
  v <- evalBinOp op v1 v2
  storeA a v
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
  VPointer τ a -> do
    guardM (blockValid (aBlock a))
    guard (aInRange a)
    nextExpr es k (ELVal (LVal τ a))
  _            -> nothingT
redexStep es (RedLField k su i (LVal _ a))   = do
  a' <- aBranch su i a -- fails if a is indeterminate
  nextExpr es k (ELVal (lVal a'))

valStep :: EInSCtx b -> b -> CMaybe E
valStep (EInSCtx k es ae tmps) a = do
  _ <- mapM freeUnchecked tmps -- free all objects with temporary storage
  case es of
    CtxVLDeclT x s -> do
      b <- alloc a Nothing MAuto
      return (ES (CtxVLDecl x ae b:k, s))
    CtxExpr        -> nextStmt (k, SExpr ae)
    CtxReturn      -> funReturn a (k, SReturn (Just ae)) -- a could have been freed
    CtxIfE st sf   -> do
      b <- maybeT (valToBool a) -- a could have been freed
      if b
      then return (ES (CtxIfT ae sf:k, st))
      else return (ES (CtxIfF ae st:k, sf))
    CtxSwitchE s   -> case a of
      VInt n -> ES <$> toCase n (CtxSwitch ae:k, s)
      _      -> nothingT

{- Glueing it all together -}
step :: E -> CMaybe E
step (ES sk)   = stmtStep sk
step (EE es e) = case split e of
  Left b    -> valStep es b
  Right rds -> redexStep es (head rds) -- Just pick the first ;)
step (EF _)    = nothingT

eval :: E -> CMaybe Val
eval (EF v) = return v
eval e      = {- trace (show e ++ "\n") $ -} step e >>= eval

evalStmt :: Stmt -> CMaybe Val
evalStmt s = eval (ES ([], s))

evalFun :: Id -> CMaybe Val
evalFun x = do
  Fun _ _ s <- getFun x
  evalStmt s

