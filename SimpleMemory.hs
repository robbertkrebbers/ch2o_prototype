{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XStandaloneDeriving #-}
{-# OPTIONS -XGADTs #-}
{-# OPTIONS -XKindSignatures #-}
{-# OPTIONS -XTypeSynonymInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XUndecidableInstances #-}
{-# OPTIONS -XFunctionalDependencies #-}

module SimpleMemory where

import Util
import Types
import Values

import Control.Monad
import Control.Applicative
import Control.Monad.State
import Control.Monad.Maybe
import Control.Monad.Error
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

{- Blocks -}
type Block = Int

class BlockOf a where
  blockOf :: a -> Block

{- Addresses -}
data Addr :: * -> (* -> *) -> * where
  Addr  :: Block -> Ref c AVal AVal -> Int -> Addr c Val
  AddrA :: Block -> Ref c AVal AVal -> Addr c AVal

deriving instance Eq c   => Eq (Addr c w)
deriving instance Show c => Show (Addr c w)

addr :: Block -> Addr c Val
addr b = Addr b RHere 0

instance BlockOf (Addr c v) where
  blockOf (Addr b _ _) = b
  blockOf (AddrA b _)  = b

aOffset :: Addr c w -> Int
aOffset (Addr b _ _) = b
aOffset (AddrA b _)  = b

aRef :: Addr c w -> Ref c AVal AVal
aRef (Addr _ p _) = p
aRef (AddrA _ p)  = p

aNormalize :: Cis c => Addr c v -> Ref c AVal v
aNormalize (Addr _ p i) = branchA i p
aNormalize (AddrA _ p)  = p

instance Cis c => SimpleReference (Addr c) where
  branch su i a         = AddrA (blockOf a) (branch su i (aNormalize a))
  branchA i (AddrA b p) = Addr b p i

aMove :: Int -> Addr c Val -> Addr c Val
aMove x (Addr b p i) = Addr b p (i + x)

aBranch :: Cis c => StructUnion -> Int -> Addr c Val -> Addr c Val
aBranch su i = branchA 0 . branch su i

instance Related (Addr c v) where
  Addr b1 p1 i1 `related` Addr b2 p2 i2 = b1 == b2 && p1 `related` p2 && i1 == i2
  AddrA b1 p1   `related` AddrA b2 p2   = b1 == b2 && p1 `related` p2
  _             `related` _             = error "impossible"

aCisReset :: Cis d => Addr c v -> Addr d v
aCisReset (Addr b p i) = Addr b (rCisReset p) i
aCisReset (AddrA b p)  = AddrA b (rCisReset p)

{- Memory -}
data MFlag = MStatic | MAuto | MTemp | MMalloc | MFreed deriving (Eq, Show)
data MSpace a = MSpace { cVal :: AVal a, cFlag :: MFlag } deriving (Eq, Show)

instance Functor MSpace where
  fmap f (MSpace v fl) = MSpace (fmap f v) fl
instance BTypeOf a => TypeOf (MSpace a) where
  typeOf = typeOf . cVal

data SimpleMem a = SimpleMem {
  mEnv   :: Env,
  blocks :: IntMap (MSpace a)
} deriving (Eq, Show)

instance Functor SimpleMem where
  fmap f (SimpleMem e bs) = SimpleMem e (fmap f <$> bs)

class (EnvReader m, BTypeOf a, Defined a) => SimpleMemReader a m | m -> a where
  getMem :: m (SimpleMem a)
class SimpleMemReader a m => SimpleMemWriter a m | m -> a where
  setMem :: SimpleMem a -> m ()
instance EnvReader (State (SimpleMem a)) where
  getEnv = gets mEnv
instance (BTypeOf a, Defined a) => SimpleMemReader a (State (SimpleMem a)) where
  getMem = get
instance SimpleMemReader a m => SimpleMemReader a (MaybeT m) where
  getMem = lift getMem
instance SimpleMemWriter a m => SimpleMemWriter a (MaybeT m) where
  setMem = lift . setMem
instance (SimpleMemReader a m, Error e) => SimpleMemReader a (ErrorT e m) where
  getMem = lift getMem
instance (SimpleMemWriter a m, Error e) => SimpleMemWriter a (ErrorT e m) where
  setMem = lift . setMem

emptyMem :: SimpleMem a
emptyMem = SimpleMem emptyEnv IntMap.empty

modifyMem :: SimpleMemWriter a m => (SimpleMem a -> SimpleMem a) -> m ()
modifyMem f = getMem >>= setMem . f

getSpace :: SimpleMemReader a m => Block -> MaybeT m (MSpace a)
getSpace b = getMem >>= maybeT . IntMap.lookup b . blocks

getSpaceAVal :: SimpleMemReader a m => Block -> MaybeT m (AVal a)
getSpaceAVal = fmap cVal . getSpace

flagOfBlock :: SimpleMemReader a m => Block -> MaybeT m MFlag
flagOfBlock b = cFlag <$> getSpace b

blockValid :: SimpleMemReader a m => Block -> m Bool
blockValid b = fromMaybeT False $ do
  f <- flagOfBlock b
  return (f /= MFreed)

typeOfBlock :: SimpleMemReader a m => Block -> MaybeT m Type
typeOfBlock b = typeOf <$> getSpace b

instance (BTypeOf a, SimpleMemReader a m) => Check m (Addr c Val) where
  check (Addr b p i) = fromMaybeT False $ do
    τb <- typeOfBlock b
    τ <- target p τb
    return (0 <= i && i <= arrayWidth τ)

simpleAlloc :: SimpleMemWriter a m => AVal a -> MFlag -> m Block
simpleAlloc v f = do
  SimpleMem e bs <- getMem
  let n = IntMap.size bs in do
  setMem (SimpleMem e (IntMap.insert n (MSpace v f) bs))
  return n

simpleFree :: SimpleMemWriter a m => Bool -> Block -> MaybeT m ()
simpleFree mal b = do
  MSpace w f <- getSpace b
  guard (f /= MFreed && (not mal || f == MMalloc))
  modifyMem $ \m -> m { blocks = IntMap.insert b (MSpace w MFreed) (blocks m) }

simpleLoad :: (SimpleMemReader a m, Cis c) => Addr c v -> MaybeT m (v a)
simpleLoad a = do
  MSpace w f <- getSpace (blockOf a)
  guard (f /= MFreed)
  follow (aNormalize a) w

simpleUpdate :: (SimpleMemWriter a m, Cis c) => (v a -> MaybeT m (v a)) -> Addr c v -> MaybeT m ()
simpleUpdate up a = do
  MSpace w f <- getSpace (blockOf a)
  guard (f /= MFreed && f /= MTemp && not (isConst w))
  w' <- vUpdate up (aNormalize a) w
  modifyMem $ \m -> m { blocks = IntMap.insert (blockOf a) (MSpace w' f) (blocks m) }

simpleStore :: (SimpleMemWriter a m, Cis c) => Addr c v -> v a -> MaybeT m ()
simpleStore a v = simpleUpdate (\_ -> return v) a

