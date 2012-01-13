{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XUndecidableInstances #-}
{-# OPTIONS -XFlexibleContexts #-}

module Memory where

import Util
import Types
import Values
import SimpleMemory
import Pointers
import RLValues

import Prelude
import Control.Monad.Maybe
import Control.Applicative

{- Memory -}
type MPointer = Pointer ()
type MBVal = BVal MPointer
type MVal  = Val MBVal
type MAVal = AVal MBVal
type Mem   = SimpleMem MBVal

class SimpleMemReader MBVal m => MemReader m where
instance SimpleMemReader MBVal m => MemReader m where
class SimpleMemWriter MBVal m => MemWriter m where
instance SimpleMemWriter MBVal m => MemWriter m where

alloc :: MemWriter m => Type -> Maybe RAVal -> MFlag -> MaybeT m Block
alloc _ (Just v) f = simpleAlloc (fmap pCisReset <$> v) f
alloc τ Nothing  f = do
  v <- newAVal newB τ
  simpleAlloc v f
 where newB = if f == MStatic then zeroBVal else VUndef

free :: MemWriter m => Bool -> Block -> MaybeT m ()
free = simpleFree

load :: MemWriter m => LVal -> MaybeT m RVal
load lv = do
  a <- maybeT (pAddr lv)
  v <- simpleLoad a
  guardM (isDeterminate v)
  return (fmap pCisReset <$> v)

store :: MemWriter m => LVal -> RVal -> MaybeT m ()
store lv rv = do
  a <- maybeT (pAddr lv)
  simpleStore a (fmap pCisReset <$> rv)

aToVal :: MemWriter m => RAVal -> MaybeT m (Maybe Block, RVal)
aToVal ar@(VArray (TArray τ n) _) = do
  b <- alloc (TArray τ n) (Just ar) MTemp
  return (Just b, VBase False $ VPointer $ Pointer (addr b) (TArray τ n)  0 τ)
aToVal (VArray _ [v])             = guardM (isDeterminate v) >> return (Nothing, v)
aToVal (VArray _ _)               = nothingT

