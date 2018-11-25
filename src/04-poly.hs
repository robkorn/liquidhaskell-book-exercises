
{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module VectorBounds
   ( safeLookup
   , unsafeLookup
   , vectorSum, vectorSum'
   , absoluteSum, absoluteSum'
   , dotProduct
   , sparseProduct, sparseProduct'
   , eeks
   , head, head', head''
   ) where

import Prelude      hiding (head, abs, length)
import Data.List    (foldl')
import Data.Vector  hiding (head, foldl')

absoluteSum'     :: Vector Int -> Int
dotProduct     :: Vector Int -> Vector Int -> Int
absoluteSum     :: Vector Int -> Int
sparseProduct, sparseProduct'  :: Vector Int -> [(Int, Int)] -> Int

eeks      = [ok, yup, nono]
  where
    ok    = twoLangs ! 0
    yup   = twoLangs ! 1
    nono  = twoLangs ! 3
{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}
{-@ twoLangs :: VectorN String 2 @-}
twoLangs     = fromList ["haskell", "javascript"]

{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

head     :: Vector a -> a
head vec = vec ! 0

{-@ type NEVector a = {v:Vector a | 0 < vlen v} @-}

{-@ head' :: NEVector a -> a @-}
head' vec = vec ! 0

head''     :: Vector a -> Maybe a
head'' vec = case Data.Vector.null vec of
               false -> Just $ vec ! 0

{-@ unsafeLookup :: Int -> Vector a -> a @-}
unsafeLookup index vec = vec ! index

{-@ safeLookup :: Vector a -> Int -> Maybe a @-}
safeLookup x i
  | ok        = Just (x ! i)
  | otherwise = Nothing
  where
    ok        = undefined

-- >>> vectorSum (fromList [1, -2, 3])
-- 2
vectorSum         :: Vector Int -> Int
vectorSum vec     = go 0 0
  where
    go acc i
      | i < sz    = go (acc + (vec ! i)) (i + 1)
      | otherwise = acc
    sz            = length vec

-- >>> absoluteSum (fromList [1, -2, 3])
-- 6
{-@ absoluteSum :: Vector Int -> Nat @-}
absoluteSum     = undefined


{-@ go :: Int -> {v:Int | 0 <= v && v <= sz} -> Int @-}


loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f =  go base lo
  where
    go acc i
      | i < hi    = go (f i acc) (i + 1)
      | otherwise = acc

vectorSum'      :: Vector Int -> Int
vectorSum' vec  = loop 0 n 0 body
  where
    body i acc  = acc + (vec ! i)
    n           = length vec

-- >>> absoluteSum' (fromList [1, -2, 3])
-- 6
{-@ absoluteSum' :: Vector Int -> Nat @-}
absoluteSum' vec = loop 0 n 0 body
  where
    body i acc   = undefined
    n            = length vec

-- >>> dotProduct (fromList [1,2,3]) (fromList [4,5,6])
-- 32
{-@ dotProduct :: x:Vector Int -> y:Vector Int -> Int @-}
dotProduct x y = loop 0 sz 0 body
  where
    body i acc = acc + (x ! i)  *  (y ! i)
    sz         = length x

{-@ type SparseN a N = [(Btwn 0 N, a)] @-}

{-@ sparseProduct  :: x:Vector _ -> SparseN _ (vlen x) -> _ @-}
sparseProduct x y   = go 0 y
  where
    go n []         = n
    go n ((i,v):y') = go (n + (x!i) * v) y'

{-@ sparseProduct'  :: x:Vector _ -> SparseN _ (vlen x) -> _ @-}
sparseProduct' x y  = foldl' body 0 y
  where
    body sum (i, v) = sum + (x ! i) * v
