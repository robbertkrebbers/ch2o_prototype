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
  pAddr     :: Addr c Val,
  pObjType  :: Type,
  pType     :: Type
} deriving (Eq, Show)

instance BlockOf (Pointer c) where
  blockOf = blockOf . pAddr

instance TypeOf (Pointer c) where
  typeOf = pType

pLength :: Pointer c -> Int
pLength = arrayWidth . pObjType

pRef :: Pointer c -> Ref c AVal AVal
pRef = aRef . pAddr

pOffset :: Pointer c -> Int
pOffset = aOffset . pAddr

pInRange :: Pointer c -> Bool
pInRange p = 0 <= pOffset p && pOffset p < pLength p

pIsAlligned :: Pointer c -> Bool
pIsAlligned (Pointer _ _ TVoid) = True
pIsAlligned (Pointer a σ τ)     = τ <= σ && aOffset a `quot` arrayWidth τ == 0

pCisReset :: Cis d => Pointer c -> Pointer d
pCisReset p = p { pAddr = aCisReset (pAddr p) }

pCast :: Pointer c -> Type -> Maybe (Pointer c)
pCast (Pointer a σ _) τ = 
  let p' = Pointer a σ τ in do
  guard (pIsAlligned p')
  return p'

instance (BTypeOf a, SimpleMemReader a m) => Check m (Pointer c) where
  check p = check (pAddr p) &&? return (0 <= pOffset p && pOffset p <= pLength p && pIsAlligned p)

blockPointer :: SimpleMemReader a m => Block -> MaybeT m (Pointer c)
blockPointer b = do
  τ <- typeOfBlock b
  return (Pointer (addr b) τ τ)

pPlus :: Int -> Pointer c -> Maybe (Pointer c)
pPlus x (Pointer a σ τ) =
  let a'  = aMove (fromEnum x * arrayWidth τ) a in do
  guard (0 <= aOffset a' && aOffset a' < arrayWidth σ)
  Just (Pointer a' σ τ)

pMinus :: Pointer c -> Pointer c -> Maybe Int
pMinus (Pointer a1 _ τ1) (Pointer a2 _ τ2) = do
  guard (blockOf a1 == blockOf a2)
  guard (aRef (aCisReset a1 :: Addr () Val) == aRef (aCisReset a1 :: Addr () Val))
  guard (τ1 == τ2)
  let n = aOffset a1 - aOffset a2 in do
  guard (n `rem` arrayWidth τ1 == 0)
  Just (n `quot` arrayWidth τ1)

instance SimpleMemReader a m => Determinate m (Pointer c) where
  isDeterminate = blockValid . blockOf

pBranch :: (SimpleMemReader a m, Cis c) => StructUnion -> Int -> Pointer c -> MaybeT m (Pointer c)
pBranch su i p = case typeOf p of
  TStruct su' c s | su == su' -> do
    guardM (isDeterminate p)
    τ <- field su c s i
    return (Pointer (aBranch su i (pAddr p)) τ τ)
  _                           -> nothingT

instance SimpleMemReader a m => FuzzyOrd (MaybeT m) (Pointer c) where
  p ==? q | blockOf p == blockOf q = do
    guardM (isDeterminate p)
    r <- maybeT (pRef p ==? pRef q)
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
    r <- maybeT (pRef p ==? pRef q)
    if r
    then return (pOffset p <= pOffset q)
    else guard (pInRange p && pInRange q) >> maybeT (pRef p <=? pRef q)
  _ <=? _ | otherwise            = nothingT

{-
aMap :: (Block -> Maybe Block) -> Addr -> Maybe Addr
aMap f (Addr a p τ i) = do b <- f a; Just (Addr b p τ i)
-}

