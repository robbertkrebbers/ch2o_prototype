{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# OPTIONS -XTypeSynonymInstances #-}
{-# OPTIONS -XRankNTypes #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XFlexibleContexts #-}
{-# OPTIONS -XUndecidableInstances #-}

module CMonads where

import Util
import Types
import Values
import SimpleMemory
import Pointers
import Memory
import Expressions
import CSemantics

import Data.List
import System.Random
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

data CEnv = CEnv {
  cEnv     :: Env,
  cFuns    :: Map Id Fun,
  cGlobals :: Map Id Block
} deriving (Eq, Show)

data CState = CState {
  cMem     :: Mem,
  cReturns :: [Return],
  cReads   :: [Addr () Val],
  cWrites  :: [Addr () Val]
} deriving (Eq, Ord)

-- MemWriter can be derived, but Haskell thinks that results in overlapping
-- instances
class (MonadPlus m, SimpleMemWriter MBVal m) => SmartCMonad m where
  getCEnv        :: m CEnv
  getCState      :: m CState
  setCState      :: CState -> m ()
  pickSmartRedex :: [Redex a] -> m (Redex a)

modifyCState :: SmartCMonad m => (CState -> CState) -> m ()
modifyCState f = getCState >>= setCState . f

instance SmartCMonad m => CMonad m where
  getFun x           = getCEnv >>= maybeZero . Map.lookup x . cFuns
  getGlobal x        = getCEnv >>= maybeZero . Map.lookup x . cGlobals
  sequencedLoad l    = do
    a <- aCisReset <$> maybeZero (pAddr l)
    rds <- cReads <$> getCState
    wrts <- cWrites <$> getCState
    guard (all (not . related a) wrts)
    modifyCState $ \s -> s { cReads = a:rds }
    load l
  sequencedStore l r = do
    a <- aCisReset <$> maybeZero (pAddr l)
    rds <- cReads <$> getCState
    wrts <- cWrites <$> getCState
    guard (all (not . related a) (rds ++ wrts))
    modifyCState $ \s -> s { cWrites = a:wrts }
    store l r
  sequencePoint      = modifyCState $ \s -> s { cReads = [], cWrites = [] }
  pushReturn r       = modifyCState $ \s -> s { cReturns = r:cReturns s }
  popReturn          = do
    rs <- cReturns <$> getCState
    case rs of
      []      -> return Nothing
      (r:rs') -> do modifyCState $ \s -> s { cReturns = rs' }; return (Just r)
  pickRedex rs       = case find (not . hasSideEffects) rs of
    Just r  -> return r
    Nothing -> pickSmartRedex rs


data CList a = CList { 
  runCList_ :: forall c . Eq c => (Maybe a -> CEnv -> CState -> [(Maybe c, CState)]) -> CEnv -> CState -> [(Maybe c, CState)]
}

runCList :: Eq a => CList a -> CEnv -> CState -> [(Maybe a, CState)]
runCList (CList cl) = cl $ \a _ s -> [(a,s)]

instance Monad CList where
  return  x = CList ($Just x)
  CList cl >>= f = CList $ \k -> cl $ \a -> case a of
    Just a' -> runCList_ (f a') k
    Nothing -> k Nothing
instance Functor CList where
  fmap f (CList cl) = CList $ \k -> cl (k . fmap f)
instance MonadPlus CList where
  mzero                       = CList $ \k -> k Nothing
  CList cl1 `mplus` CList cl2 = CList $ \k -> cl1 $ \a -> case a of
    Just a' -> k (Just a')
    Nothing -> cl2 k
instance EnvReader CList where
  getEnv = CList $ \k e s -> k (Just (cEnv e)) e s
instance SimpleMemReader MBVal CList where
  getMem = CList $ \k e s -> k (Just (cMem s)) e s
instance SimpleMemWriter MBVal CList where
  setMem m = CList $ \k e s -> k (Just ()) e s { cMem = m }
instance SmartCMonad CList where
  getCEnv           = CList $ \k e s -> k (Just e) e s
  getCState         = CList $ \k e s -> k (Just s) e s
  setCState s       = CList $ \k e _ -> k (Just ()) e s
  pickSmartRedex rs = CList $ \k e s -> foldr union [] [k (Just r) e s | r <- rs]

data CSet a = CSet { 
  runCSet_ :: forall c . Ord c => (Maybe a -> CEnv -> CState -> Set (Maybe c, CState)) -> CEnv -> CState -> Set (Maybe c, CState)
}

runCSet :: Ord a => CSet a -> CEnv -> CState -> Set (Maybe a, CState)
runCSet (CSet cl) = cl $ \a _ s -> Set.singleton (a,s)

instance Monad CSet where
  return  x = CSet ($Just x)
  CSet cl >>= f = CSet $ \k -> cl $ \a -> case a of
    Just a' -> runCSet_ (f a') k
    Nothing -> k Nothing
instance Functor CSet where
  fmap f (CSet cl) = CSet $ \k -> cl (k . fmap f)
instance MonadPlus CSet where
  mzero                     = CSet $ \k -> k Nothing
  CSet cl1 `mplus` CSet cl2 = CSet $ \k -> cl1 $ \a -> case a of
    Just a' -> k (Just a')
    Nothing -> cl2 k
instance EnvReader CSet where
  getEnv = CSet $ \k e s -> k (Just (cEnv e)) e s
instance SimpleMemReader MBVal CSet where
  getMem = CSet $ \k e s -> k (Just (cMem s)) e s
instance SimpleMemWriter MBVal CSet where
  setMem m = CSet $ \k e s -> k (Just ()) e s { cMem = m }
instance SmartCMonad CSet where
  getCEnv           = CSet $ \k e s -> k (Just e) e s
  getCState         = CSet $ \k e s -> k (Just s) e s
  setCState s       = CSet $ \k e _ -> k (Just ()) e s
  pickSmartRedex rs = CSet $ \k e s -> Set.unions [k (Just r) e s | r <- rs]


data CRandom g a = CRandom { runCRandom_ :: CEnv -> CState -> g -> (Maybe a, CState, g) }

runCRandom :: RandomGen g => CRandom g a -> CEnv -> CState -> g -> (Maybe a, CState)
runCRandom m e s g = let (x,s',_) = runCRandom_ m e s g in (x,s')

instance Monad (CRandom g) where
  return x         = CRandom $ \_ s g -> (Just x,s,g)
  CRandom cr >>= f = CRandom $ \e s g -> case cr e s g of
    (Just x,s',g')    -> runCRandom_ (f x) e s' g'
    (Nothing, s', g') -> (Nothing, s', g')
instance Functor (CRandom g) where
  fmap f (CRandom cr) = CRandom $ \e s g -> let (x,s',g') = cr e s g in (f <$> x, s', g')
instance MonadPlus (CRandom g) where
  mzero                           = CRandom $ \_ s g -> (Nothing, s, g)
  CRandom cl1 `mplus` CRandom cl2 = CRandom $ \e s g -> case cl1 e s g of
    (Just x,s',g')  -> (Just x,s',g')
    (Nothing, _, _) -> cl2 e s g
instance EnvReader (CRandom g) where
  getEnv = CRandom $ \e s g -> (Just (cEnv e), s, g)
instance SimpleMemReader MBVal (CRandom g) where
  getMem = CRandom $ \_ s g -> (Just (cMem s), s, g)
instance SimpleMemWriter MBVal (CRandom g) where
  setMem m = CRandom $ \_ s g -> (Just (), s { cMem = m }, g)
instance RandomGen g => SmartCMonad (CRandom g) where
  getCEnv           = CRandom $ \e s g -> (Just e, s, g)
  getCState         = CRandom $ \_ s g -> (Just s, s, g)
  setCState s       = CRandom $ \_ _ g -> (Just (), s, g)
  pickSmartRedex rs = CRandom $ \_ s g -> let (i, g') = next g in (Just (rs !! abs (i `rem` length rs)), s, g')

