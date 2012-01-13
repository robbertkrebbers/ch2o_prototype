{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XUndecidableInstances #-}

module Pointers where

import Util
import Types
import Values
import SimpleMemory

import Control.Monad
import Control.Monad.Maybe

{- Pointers -}
data Pointer c = Pointer {
  pObjAddr  :: Addr c AVal,
  pObjType  :: Type,
  pOffset   :: Int,
  pType     :: Type
} deriving (Eq, Show)

instance BlockOf (Pointer c) where
  blockOf = blockOf . pObjAddr

instance TypeOf (Pointer c) where
  typeOf = pType

pLength :: Pointer c -> Int
pLength = arrayWidth . pObjType

pInRange :: Pointer c -> Bool
pInRange p = 0 <= pOffset p && pOffset p < pLength p

pAddr :: Cis c => Pointer c -> Maybe (Addr c Val)
pAddr p = do
  guard (pInRange p)
  Just (branchA (pOffset p) (pObjAddr p))

pIsAlligned :: Pointer c -> Bool
pIsAlligned (Pointer _ _ _ TVoid) = True
pIsAlligned (Pointer _ τa i τ)    = τ <= τa && i `quot` arrayWidth τ == 0

pCisReset :: Cis d => Pointer c -> Pointer d
pCisReset p = p { pObjAddr = aCisReset (pObjAddr p) }

pCast :: Pointer c -> Type -> Maybe (Pointer c)
pCast (Pointer a aτ i _) σ = 
  let p' = Pointer a aτ i σ in do
  guard (pIsAlligned p')
  return p'

instance (BTypeOf a, SimpleMemReader a m) => Check m (Pointer c) where
  check p = check (pObjAddr p) &&? return (0 <= pOffset p && pOffset p <= pLength p && pIsAlligned p)

blockPointer :: SimpleMemReader a m => Block -> MaybeT m (Pointer c)
blockPointer b = do
  τ <- typeOfBlock b
  return (Pointer (addr b) τ 0 τ)

pPlus :: Int -> Pointer c -> Maybe (Pointer c)
pPlus x (Pointer a τa i τ) =
  let i'  = i + fromEnum x * arrayWidth τ in do
  guard (0 <= i' && i' < arrayWidth τa)
  Just (Pointer a τa i' τ)

pMinus :: Pointer c -> Pointer c -> Maybe Int
pMinus (Pointer a1 _ i1 τ1) (Pointer a2 _ i2 τ2) = do
  guard (blockOf a1 == blockOf a2)
  guard (aRef (aCisReset a1 :: Addr () AVal) == aRef (aCisReset a1 :: Addr () AVal))
  guard (τ1 == τ2)
  let n = i1 - i2 in do
  guard (n `rem` arrayWidth τ1 == 0)
  Just (n `quot` arrayWidth τ1)

instance SimpleMemReader a m => Determinate m (Pointer c) where
  isDeterminate = blockValid . blockOf

pBranch :: (SimpleMemReader a m, Cis c) => StructUnion -> Int -> Pointer c -> MaybeT m (Pointer c)
pBranch su i p = case typeOf p of
  TStruct su' c s | su == su' -> do
    guardM (isDeterminate p)
    τ <- field su c s i
    a <- maybeT (pAddr p)
    return (Pointer (branch su i a) τ 0 τ)
  _                           -> nothingT

instance SimpleMemReader a m => FuzzyOrd (MaybeT m) (Pointer c) where
  p ==? q | blockOf p == blockOf q = do
    guardM (isDeterminate p)
    r <- maybeT (aRef (pObjAddr p) ==? aRef (pObjAddr q))
    if r
    then return (pOffset p == pOffset q)
    else guard (pInRange p && pInRange q) >> return False
  p ==? q | otherwise            = do
    guardM (isDeterminate p)
    guardM (isDeterminate q)
    fp <- flagOfBlock (blockOf p)
    fq <- flagOfBlock (blockOf q)
    guard (fp /= MTemp && fq /= MTemp)
    τp <- typeOfBlock (blockOf p)
    τq <- typeOfBlock (blockOf q)
    guard (not (isConst τp) && not (isConst τq))
    guard (pInRange p && pInRange q)
    return False

  p <=? q | blockOf p == blockOf q = do
    guardM (isDeterminate p)
    r <- maybeT (aRef (pObjAddr p) ==? aRef (pObjAddr q))
    if r
    then return (pOffset p <= pOffset q)
    else guard (pInRange p && pInRange q) >> maybeT (aRef (pObjAddr p) <=? aRef (pObjAddr q))
  _ <=? _ | otherwise            = nothingT

{-
aMap :: (Block -> Maybe Block) -> Addr -> Maybe Addr
aMap f (Addr a p τ i) = do b <- f a; Just (Addr b p τ i)
-}

