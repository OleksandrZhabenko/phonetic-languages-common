-- |
-- Module      :  Languages.UniquenessPeriods.Vector.DataG
-- Copyright   :  (c) OleksandrZhabenko 2020
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  olexandr543@yahoo.com
--
-- Is a generalization of the DobutokO.Poetry.Data module
-- functionality from the @dobutokO-poetry-general@ package.
--

{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}

module Languages.UniquenessPeriods.Vector.DataG where

import qualified Data.Vector as VB
import Data.SubG
import Data.SubG.InstancesPlus

type UniquenessG1T2 t t2 a b = (t2 b,VB.Vector b, t a)

-- | The list in the 'PA' variant represent the prepending @[a]@ and the postpending one respectively. 'K' constuctor actually means no prepending and
-- postpending (usually of the text). Both are used basically to control the behaviour of the functions.
data PreApp t a = K | PA (t a) (t a) deriving Eq

class (Foldable t) => UGG1 t a b where
  get1m :: a -> t b
  get2m :: a -> t b
  getm :: Bool -> a -> t b
  getm True = get1m
  getm _ = get2m
  preapp :: a -> t (t b) -> t (t b)
  setm :: t b -> t b -> a

instance Eq a => UGG1 [] (PreApp [] a) a where
  get1m K = []
  get1m (PA xs _) = xs
  get2m K = []
  get2m (PA _ ys) = ys
  preapp K xss = xss
  preapp (PA xs ys) yss = xs:yss ++ [ys]
  setm [] [] = K
  setm xs ys = PA xs ys

instance Eq a => UGG1 VB.Vector (PreApp VB.Vector a) a where
  get1m K = VB.empty
  get1m (PA v _) = v
  get2m K = VB.empty
  get2m (PA _ v) = v
  preapp K v = v
  preapp (PA v1 v2) v3 = preAppend v1 (VB.singleton v2) v3
  setm v1 v2
    | VB.null v1 && VB.null v2 = K
    | otherwise = PA v1 v2

isPA :: PreApp t a -> Bool
isPA K = False
isPA _ = True

isK :: PreApp t a -> Bool
isK K = True
isK _ = False

data UniquenessG2 a b = UL2 (VB.Vector a,b) deriving Eq

instance (Show a, Show b, InsertLeft t a, Foldable t2, Show (t2 b), Show (t a)) => Show (UniquenessG2 (UniquenessG1T2 t t2 a b) (VB.Vector (UniquenessG1T2 t t2 a b))) where
  show (UL2 (ws,_)) = show ws

type UniqG2T2 t t2 a b = UniquenessG2 (UniquenessG1T2 t t2 a b) (VB.Vector (UniquenessG1T2 t t2 a b))

get22 :: UniqG2T2 t t2 a b -> (VB.Vector (UniquenessG1T2 t t2 a b), VB.Vector (UniquenessG1T2 t t2 a b))
get22 (UL2 (ws, x)) = (ws, x)

-- | Is used to avoid significant code duplication.
data FuncRep a b c = U1 (a -> c) | D2 (a -> b) (b -> c)

getAC :: FuncRep a b c -> (a -> c)
getAC (U1 f) = f
getAC (D2 g1 g2) = g2 . g1

isU1 :: FuncRep a b c -> Bool
isU1 (U1 _) = True
isU1 _ = False

isD2 :: FuncRep a b c -> Bool
isD2 (D2 _ _) = True
isD2 _ = False

