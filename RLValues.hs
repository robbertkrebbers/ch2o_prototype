{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS -XFlexibleInstances #-}
{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XUndecidableInstances #-}
{-# OPTIONS -XFlexibleContexts #-}

module RLValues where

import Values
import Pointers

type RPointer = Pointer Bool
type RBVal = BVal RPointer
type RVal  = Val RBVal
type RAVal = AVal RBVal
type LVal  = RPointer

