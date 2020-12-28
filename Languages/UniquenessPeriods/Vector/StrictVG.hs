-- |
-- Module      :  Languages.UniquenessPeriods.Vector.StrictVG
-- Copyright   :  (c) OleksandrZhabenko 2020
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  olexandr543@yahoo.com
--
-- Generalization of the DobutokO.Poetry.StrictV module functionality from
-- the @dobutokO-poetry-general@ package.
-- Can be used to get possible permutations of no more than 7 substructures
-- in the 'F.Foldable' structure separated with the elements of the \"whitespace symbols\"
-- structure.

{-# LANGUAGE CPP, BangPatterns, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}

module Languages.UniquenessPeriods.Vector.StrictVG (
  universalSetG
  , result
  , resultB
  , uniquenessVariants2GN
  , uniquenessVariants2GNB
  , uniquenessVariants2GNP
  , uniquenessVariants2GNPB
  , genPermutations
  , genPermutationsV
) where

import qualified Data.Vector.Unboxed as V
import qualified Data.Vector as VB
import qualified Data.List as L (permutations)
import Languages.UniquenessPeriods.Vector.DataG
import qualified Data.Foldable as F
import Data.SubG
import Data.Monoid

-- | A generalized variant of the 'uniquenessVariants2GN' function from the @uniqueness-periods-vector-common@ package which, moreover, allows to specify the used permutations.
uniquenessVariants2GNB ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Ord b, Foldable t2) => a -- ^ The first most common element in the \"whitespace symbols\" structure
  -> (t a -> VB.Vector a) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of @a@ so that the function can process further the permutations
  -> ((t (t a)) -> VB.Vector (VB.Vector a)) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of 'VB.Vector' of @a@ so that the function can process further
  -> (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (VB.Vector Int) -- ^ The list of permutations of 'Int' indices starting from 0 and up to n (n is probably less than 8).
  -> VB.Vector (t2 b -> b)
  -> FuncRep (t a) (VB.Vector c) (t2 b) -- ^ It includes the defined earlier variant with data constructor 'D2', but additionally allows to use just single argument with data constructor 'U1'
  -> t (t a) -- ^ Must be obtained as 'subG' @whspss xs@
  -> VB.Vector (t2 b,VB.Vector b, t a)
uniquenessVariants2GNB !hd f1 f2 f3 perms vN frep !subs = uniquenessVariants2GNPB mempty mempty hd f1 f2 f3 perms vN frep subs
{-# INLINE uniquenessVariants2GNB #-}

-- | A variant of the 'uniquenessVariants2GNB' with the usage of the 'V.Vector' @c@ (an unboxed one) instead of the boxed variant 'VB.Vector' @c@. If @c@ is an instance of the
-- 'V.Unboxed' class then possibly it can be better from the performance point of view to use this variant.
uniquenessVariants2GN ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Ord b, Foldable t2) =>  a -- ^ The first most common element in the whitespace symbols structure
  -> (t a -> VB.Vector a) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of @a@ so that the function can process further the permutations
  -> ((t (t a)) -> VB.Vector (VB.Vector a)) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of 'VB.Vector' of @a@ so that the function can process further
  -> (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (VB.Vector Int) -- ^ The list of permutations of 'Int' indices starting from 0 and up to n (n is probably less than 8).
  -> VB.Vector (t2 b -> b)
  -> FuncRep (t a) (V.Vector c) (t2 b) -- ^ It includes the defined earlier variant with data constructor 'D2', but additionally allows to use just single argument with data constructor 'U1'
  -> t (t a) -- ^ Must be obtained as 'subG' @whspss xs@
  -> VB.Vector (t2 b,VB.Vector b, t a)
uniquenessVariants2GN !hd f1 f2 f3 perms vN frep !subs = uniquenessVariants2GNP mempty mempty hd f1 f2 f3 perms vN frep subs
{-# INLINE uniquenessVariants2GN #-}

-- | Generalized variant of 'uniquenessVariants2GN' with prepending and appending @[a]@ (given as the first and the second argument).
uniquenessVariants2GNPB ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Ord b, Foldable t2) => t a
  -> t a
  ->  a -- ^ The first most common element in the whitespace symbols structure
  -> (t a -> VB.Vector a) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of @a@ so that the function can process further the permutations
  -> ((t (t a)) -> VB.Vector (VB.Vector a)) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of 'VB.Vector' of @a@ so that the function can process further
  -> (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (VB.Vector Int) -- ^ The list of permutations of 'Int' indices starting from 0 and up to n (n is probably less than 7).
  -> VB.Vector (t2 b -> b)
  -> FuncRep (t a) (VB.Vector c) (t2 b) -- ^ Since version 0.5.0.0 it includes the previous variant with data constructor 'D2', but additionally allows to use just single argument with data constructor 'U1'
  -> t (t a) -- ^ Must be obtained as @subG whspss xs@
  -> VB.Vector (t2 b,VB.Vector b, t a)
uniquenessVariants2GNPB !ts !us !hd f1 f2 f3 perms vN frep !subs
  | F.null subs = VB.empty
  | otherwise =
     let !uss = (hd %@ us) %^ mempty
         !baseV = VB.map (hd `VB.cons`) . f2 $ subs
         !ns = universalSetG ts uss f1 f2 perms baseV in VB.map (resultB f3 vN frep) ns

-- | Is used internally in the 'uniquenessVariants2GNPB', 'uniquenessVariants2GNP' and related functions. A key point of the evaluation -- the universal set of the task represented as a
-- 'VB.Vector' of 'VB.Vector' of @a@.
universalSetG ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a))) => t a
  -> t (t a)
  -> (t a -> VB.Vector a) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of @a@ so that the function can process further the permutations
  -> ((t (t a)) -> VB.Vector (VB.Vector a)) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (VB.Vector Int) -- ^ The list of permutations of 'Int' indices starting from 0 and up to n (n is probably less than 7).
  -> VB.Vector (VB.Vector a)
  -> VB.Vector (VB.Vector a)
universalSetG ts uss f1 f2 perms baseV = VB.map (VB.foldr' mappend mempty . VB.cons (f1 ts) . (`mappend` (f2 uss)) . VB.unsafeBackpermute baseV) perms
{-# INLINE universalSetG #-}

-- | A variant of the 'uniquenessVariants2GNPB' with the usage of the 'V.Vector' @c@ (an unboxed one) instead of the boxed variant 'VB.Vector' @c@. If @c@ is an instance of the
-- 'V.Unboxed' class then possibly it can be better from the performance point of view to use this variant.
uniquenessVariants2GNP ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a)), Ord b, Foldable t2) => t a -- ^ The prepending structure.
  -> t a -- ^ The postpending structure.
  -> a -- ^ The first most common element in the whitespace symbols structure.
  -> (t a -> VB.Vector a) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of @a@ so that the function can process further the permutations
  -> ((t (t a)) -> VB.Vector (VB.Vector a)) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of 'VB.Vector' of @a@ so that the function can process further
  -> (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (VB.Vector Int) -- ^ The list of permutations of 'Int' indices starting from 0 and up to n (n is probably less than 7).
  -> VB.Vector (t2 b -> b)
  -> FuncRep (t a) (V.Vector c) (t2 b) -- ^ It includes the defined earlier variant with data constructor 'D2', but additionally allows to use just single argument with data constructor 'U1'
  -> t (t a) -- ^ Must be obtained as 'subG' @whspss xs@
  -> VB.Vector (t2 b,VB.Vector b, t a)
uniquenessVariants2GNP !ts !us !hd f1 f2 f3 perms vN frep !subs
  | F.null subs = VB.empty
  | otherwise =
     let !uss = (hd %@ us) %^ mempty
         !baseV = VB.map (hd `VB.cons`) . f2 $ subs
         !ns = universalSetG ts uss f1 f2 perms baseV in VB.map (result f3 vN frep) ns

result ::
  (Eq a, Foldable t, Foldable t2) =>
  (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (t2 b -> b)
  -> FuncRep (t a) (V.Vector c) (t2 b) -- ^ It includes the defined earlier variant with data constructor 'D2', but additionally allows to use just single argument with data constructor 'U1'
  -> VB.Vector a
  -> (t2 b,VB.Vector b, t a)
result f3 vN frep vs =
  (rs, (VB.map (\f -> f rs) vN), ws)
    where !ws = f3 vs
          !rs = getAC frep ws
{-# INLINE result #-}

resultB ::
  (Eq a, Foldable t, Foldable t2) =>
  (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (t2 b -> b)
  -> FuncRep (t a) (VB.Vector c) (t2 b) -- ^ It includes the defined earlier variant with data constructor 'D2', but additionally allows to use just single argument with data constructor 'U1'
  -> VB.Vector a
  -> (t2 b,VB.Vector b, t a)
resultB f3 vN frep vs =
  (rs, (VB.map (\f -> f rs) vN), ws)
    where !ws = f3 vs
          !rs = getAC frep ws
{-# INLINE resultB #-}

genPermutations :: Int -> VB.Vector (VB.Vector Int)
genPermutations n = VB.map VB.fromList . VB.fromList . L.permutations . take n $ [0..]
{-# INLINE genPermutations #-}

genPermutationsV :: VB.Vector (VB.Vector (VB.Vector Int))
genPermutationsV = VB.map (\n -> VB.map VB.fromList . VB.fromList . L.permutations . take n $ [0..]) . VB.enumFromTo 2 $ 7
{-# INLINE genPermutationsV #-}
