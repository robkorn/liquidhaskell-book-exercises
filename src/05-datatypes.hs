{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}
module RefinedDatatypes
       (
         -- * Sparse: Data
         Sparse (..)

         -- * Sparse: Functions
       , dotProd, dotProd', plus, fromList

         -- * Sparse: Examples
       , okSP, test2

          -- * OrdList: Data
       , IncList  (..)

          -- * OrdList: Examples
       , okList, badList

          -- * OrdList: Functions
       ,  insertSort, insertSort', mergeSort, quickSort

          -- * BST: Data
       , BST (..)

          -- * BST: Functions
       , mem, add, delMin, del, bstSort, toBST, toIncList

          -- * BST: Examples
       , okBST, badBST

       )
      where

import Prelude      hiding (abs, length, min)
import Data.List    (foldl')
import Data.Vector  hiding (singleton, foldl', foldr, (++), mapM)
import Data.Maybe   (fromJust, fromMaybe)
import Data.Monoid  ((<>))
import Control.Monad (mapM)
import Control.Monad as CM (sequence)


dotProd, dotProd' :: Vector Int -> Sparse Int -> Int
test2 :: Sparse Int

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg
data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)] }
{-@ data Sparse a = SP { spDim   :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}
{-@ type Nat        = {v:Int | 0 <= v}            @-}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}
okSP :: Sparse String
okSP = SP 5 [ (0, "cat")
            , (3, "dog") ]
{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}
{-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd x (SP _ y) = go 0 y
  where
    go sum ((i, v) : y') = go (sum + (x ! i) * v) y'
    go sum []            = sum
{-@ dotProd' :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd' x (SP _ y) = foldl' body 0 y
  where
    body sum (i, v) = sum + (x ! i)  * v

--Initial Attempt. I think LH can't tell I did the check this way?
-- {-@ fromList :: d:Nat -> [(i:Int, a)] -> Maybe (SparseN a d) @-}
-- fromList          :: Int   -> [(Int, a)] -> Maybe (Sparse a)
-- fromList dim elts = fmap (SP dim) $ mapM process elts
--   where
--     process elem = let ind = fst elem
--                            in
--                        if ind < dim then Just elem else Nothing

--Attempt #2
-- {-@ fromList :: d:Nat -> [(i:Int, a)] -> Maybe (SparseN a d) @-}
-- fromList          :: Int   -> [(Int, a)] -> Maybe (Sparse a)
-- fromList dim elts = case mapM process elts of
--                       Just p -> Just $ SP dim p
--                       Nothing -> Nothing
--   where
--     process elem = let ind = fst elem
--                            in
--                        if ind < dim then Just elem else Nothing

--Attempt #3 (Hmm, it'd be nice if I could just use a theorem prover...)
-- {-@ fromList :: d:Nat -> [(i:Int, a)] -> Maybe (SparseN a d) @-}
-- fromList          :: Int   -> [(Int, a)] -> Maybe (Sparse a)
-- fromList dim elts = case (CM.sequence $ fmap process elts) of
--                       Just p -> Just $ SP dim p
--                       Nothing -> Nothing
--   where
--     process elem = let ind = fst elem
--                            in
--                        if ind < dim then Just elem else Nothing


--  {-@ test1 :: SparseN String 3 @-}
-- test1 :: Sparse String
-- test1     = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]


{-@ plus :: (Num a) => s1: Sparse a -> {s2: Sparse a | spDim s1 == spDim s2} -> {s3: Sparse a | spDim s1 == spDim s3} @-}
plus     :: (Num a) => Sparse a -> Sparse a -> Sparse a
plus (SP n xs) (SP m ys) = SP n (xs <> ys)

{-@ test2 :: SparseN Int 3 @-}
test2    = plus vec1 vec2
  where
    vec1 = SP 3 [(0, 12), (2, 9)]
    vec2 = SP 3 [(0, 8),  (1, 100)]
data IncList a =
    Emp
  | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<
{-@ data IncList a =
        Emp
      | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}  @-}

okList  = 1 :< 2 :< 3 :< Emp      -- accepted by LH

badList = 2 :< 1 :< 3 :< Emp      -- rejected by LH
insertSort        :: (Ord a) => [a] -> IncList a
insertSort []     = Emp
insertSort (x:xs) = insert x (insertSort xs)
insert             :: (Ord a) => a -> IncList a -> IncList a
insert y Emp       = y :< Emp
insert y (x :< xs)
  | y <= x         = y :< x :< xs
  | otherwise      = x :< insert y xs
insertSort'     :: (Ord a) => [a] -> IncList a
insertSort' xs  = foldr f b xs
  where
     f          = undefined    -- Fill this in
     b          = undefined    -- Fill this in
split          :: [a] -> ([a], [a])
split (x:y:zs) = (x:xs, y:ys)
  where
    (xs, ys)   = split zs
split xs       = (xs, [])
merge         :: (Ord a) => IncList a -> IncList a -> IncList a
merge xs  Emp = xs
merge Emp ys  = ys
merge (x :< xs) (y :< ys)
  | x <= y    = x :< merge xs (y :< ys)
  | otherwise = y :< merge (x :< xs) ys
mergeSort :: (Ord a) => [a] -> IncList a
mergeSort []  = Emp
mergeSort [x] = x :< Emp
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
    (ys, zs)  = split xs
quickSort           :: (Ord a) => [a] -> IncList a
quickSort []        = Emp
quickSort (x:xs)    = append x lessers greaters
  where
    lessers         = quickSort [y | y <- xs, y < x ]
    greaters        = quickSort [z | z <- xs, z >= x]

{-@ append :: x:a -> IncList a
                  -> IncList a
                  -> IncList a
  @-}
append z Emp       ys = z :< ys
append z (x :< xs) ys = x :< append z xs ys
data BST a = Leaf
           | Node { root  :: a
                  , left  :: BST a
                  , right :: BST a }
okBST :: BST Int
okBST =  Node 6
             (Node 2
                 (Node 1 Leaf Leaf)
                 (Node 4 Leaf Leaf))
             (Node 9
                 (Node 7 Leaf Leaf)
                 Leaf)
{-@ data BST a    = Leaf
                  | Node { root  :: a
                         , left  :: BSTL a root
                         , right :: BSTR a root } @-}

{-@ type BSTL a X = BST {v:a | v < X}             @-}
{-@ type BSTR a X = BST {v:a | X < v}             @-}
badBST =  Node 66
             (Node 4
                 (Node 1 Leaf Leaf)
                 (Node 69 Leaf Leaf))  -- Out of order, rejected
             (Node 99
                 (Node 77 Leaf Leaf)
                 Leaf)
mem                 :: (Ord a) => a -> BST a -> Bool
mem _ Leaf          = False
mem k (Node k' l r)
  | k == k'         = True
  | k <  k'         = mem k l
  | otherwise       = mem k r
one   :: a -> BST a
one x = Node x Leaf Leaf
add                  :: (Ord a) => a -> BST a -> BST a
add k' Leaf          = one k'
add k' t@(Node k l r)
  | k' < k           = Node k (add k' l) r
  | k  < k'          = Node k l (add k' r)
  | otherwise        = t
data MinPair a = MP { mElt :: a, rest :: BST a }
{-@ data MinPair a = MP { mElt :: a, rest :: BSTR a mElt} @-}
delMin                 :: (Ord a) => BST a -> MinPair a
delMin (Node k Leaf r) = MP k r
delMin (Node k l r)    = MP k' (Node k l' r)
  where
    MP k' l'           = delMin l
delMin Leaf            = die "Don't say I didn't warn ya!"
del                   :: (Ord a) => a -> BST a -> BST a
del k' t@(Node k l r) = undefined
del _  Leaf           = Leaf
bstSort   :: (Ord a) => [a] -> IncList a
bstSort   = toIncList . toBST

toBST     :: (Ord a) => [a] -> BST a
toBST     = foldr add Leaf

toIncList :: BST a -> IncList a
toIncList (Node x l r) = undefined
toIncList Leaf         = undefined
