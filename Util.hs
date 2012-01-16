{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XTupleSections #-}
{-# OPTIONS -XMultiParamTypeClasses #-}

module Util where

import Prelude
import Data.Maybe
import Control.Applicative
import Control.Monad.Maybe
import Control.Monad.Error
import Control.Monad.State

{- Blocks -}
type Id = String
type Assoc k a = [(k,a)]

inDom :: Eq k => k -> Assoc k a -> Bool
inDom k l = isJust (lookup k l)

update :: Eq k => k -> a -> Assoc k a -> Maybe (Assoc k a)
update _ _ []                   = Nothing
update k x ((k',_):l) | k == k' = Just $ (k,x):l
update k x (e:l)                = (e:) <$> update k x l

insertUnsafe :: Eq k => k -> a -> Assoc k a -> Assoc k a
insertUnsafe k a l = (k,a):l

insert :: Eq k => k -> a -> Assoc k a -> Maybe (Assoc k a)
insert k x l = guard (not (k `inDom` l)) >> return (insertUnsafe k x l)

assocMap :: (a -> b) -> Assoc k a -> Assoc k b
assocMap f = map $ \(k,x) -> (k,f x)

assocMapM :: Monad m => (a -> m b) -> Assoc k a -> m (Assoc k b)
assocMapM f = mapM $ \(k,x) -> liftM (k,) (f x)

(&&?) :: Monad m => m Bool -> m Bool -> m Bool
(&&?) = liftM2 (&&)

(||?) :: Monad m => m Bool -> m Bool -> m Bool
(||?) = liftM2 (||)

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM f = foldM (\b x -> f x &&? return b) True

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM f = foldM (\b x -> f x ||? return b) True

try :: MonadError e m => e -> Maybe a -> m a
try e = maybe (throwError e) return

maybeZero :: MonadPlus m => Maybe a -> m a
maybeZero = maybe mzero return 

maybeT :: Monad m => Maybe a -> MaybeT m a
maybeT = MaybeT . return

modifyMaybe :: MonadState s m => (s -> Maybe s) -> MaybeT m ()
modifyMaybe f = get >>= maybeT . f >>= put

getsMaybe :: MonadState s m => (s -> Maybe a) -> MaybeT m a
getsMaybe f = get >>= maybeT . f

fromMaybeT :: Monad m => a -> MaybeT m a -> m a
fromMaybeT d = liftM (fromMaybe d) . runMaybeT

maybeSequence :: Monad m => Maybe (m a) -> m (Maybe a)
maybeSequence Nothing  = return Nothing
maybeSequence (Just a) = do { a' <- a; return (Just a') }

maybeMapM :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
maybeMapM f = maybeSequence . fmap f

guardM :: MonadPlus m => m Bool -> m ()
guardM m = do { b <- m; if b then return () else mzero }

tryT :: Functor m => e -> MaybeT m a -> ErrorT e m a
tryT e m = ErrorT $ (maybe (Left e) Right <$> runMaybeT m)

fromBool :: a -> Bool -> Maybe a
fromBool a True  = Just a
fromBool _ False = Nothing

(!?) :: [a] -> Int -> Maybe a
l !? n = fromBool (l !! n) (n < length l)

updateAt :: Int -> a -> [a] -> [a]
updateAt _ _ []    = []
updateAt 0 x (_:l) = x:l
updateAt n x (y:l) = y:updateAt (n-1) x l

dropWhile2 :: (a -> b -> Bool) -> [a] -> [b] -> ([a], [b])
dropWhile2 f (x:xs) (y:ys) | f x y = dropWhile2 f xs ys
dropWhile2 _ xs ys                 = (xs,ys)

mapFst :: (a -> c) -> (a,b) -> (c,b)
mapFst f (a, b) = (f a, b)

mapSnd :: (b -> c) -> (a,b) -> (a,c)
mapSnd f (a, b) = (a, f b)

maybeLeft :: Either a b -> Maybe a
maybeLeft (Left a)  = Just a
maybeLeft (Right _) = Nothing

maybeRight :: Either a b -> Maybe b
maybeRight (Left _)  = Nothing
maybeRight (Right b) = Just b

infix 4 ==?, <=?

class (Monad m, Functor m) => FuzzyOrd m a where
  (==?) :: a -> a -> m Bool
  (<=?) :: a -> a -> m Bool
  
  (/=?) :: a -> a -> m Bool
  x /=? y = fmap not (x ==? y)
  
  (<?) :: a -> a -> m Bool
  x <? y = (x /=? y) &&? (x <=? y)

iFoldr :: (Int -> a -> b -> b) -> b -> Int -> [a] -> b
iFoldr _ b _ []     = b
iFoldr f b i (x:xs) = f i x (iFoldr f b (i+1) xs)

iMapM :: Monad m => (Int -> a -> m b) -> Int -> [a] -> m [b]
iMapM f = iFoldr (\i -> liftM2 (:) . f i) (return [])

