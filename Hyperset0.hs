-----------------------------------------------------------------------------
-- |
-- Module      :  Hyperset
-- Copyright   :  (c) Masahiro Sakai 2004
-- License     :  BSD-style
-- 
-- Maintainer  :  sakai@tom.sfc.keio.ac.jp
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------

module Hyperset where

import Data.Graph
import Data.Array
import Data.Maybe (isJust)
import Data.List (find)
import Data.FiniteMap

data (Ord a) => Set a = Set !Graph !(Tagging (Maybe a)) !Vertex
type Tagging u = Vertex -> u

-----------------------------------------------------------------------------

instance (Ord a) => Eq (Set a) where
    (Set g1 t1 v1) == (Set g2 t2 v2) =
        take len (rt1!v1) == take len (rt2!v2)
        where rt1 = reachabilityTable g1 t1
              rt2 = reachabilityTable g2 t2
              len = max (rangeSize (bounds g1)) (rangeSize (bounds g2))

-- emptySet :: Set a
-- mkSet :: Ord a => [a] -> Set a
-- setToList :: Set a -> [a]
-- unitSet :: a -> Set a

elementOf :: (Ord a) => Set a -> Set a -> Bool
elementOf (Set g1 t1 v1) (Set g2 t2 v2) =
    isJust (find (\child -> foo == take len (rt2!v2)) (g2!v2))
    where rt1 = reachabilityTable g1 t1
          rt2 = reachabilityTable g2 t2
          len = max (rangeSize (bounds g1)) (rangeSize (bounds g2))
          foo = take len (rt1!v1)

isEmptySet :: (Ord a) => Set a -> Bool
isEmptySet x = cardinality x == 0

cardinality :: (Ord a) => Set a -> Int
cardinality (Set g1 t1 v1) = length (g1!v1)

-----------------------------------------------------------------------------

{- FIXME: ˜AŒ‹¬•ª–ˆ‚ÉƒOƒ‰ƒt‚ð•ª‚¯‚é -}
mkSets :: (Ord u) => Graph -> Tagging (Maybe u) -> Table (Set u)
mkSets g t = array (bounds g) [(v, Set g' t' (m1!v)) | v <- indices g]
    where (g',m1,m2) = mkCanonicalPicture g t
          t' v = t (m2!v)

mkCanonicalPicture :: (Ord u) => Graph -> Tagging u ->
                      (Graph, Table Vertex, Table Vertex)
mkCanonicalPicture g t = (g',m1,m2)
    where q  = classifyNode g t
          g' = buildG (0, length q - 1) [(m1!a,m1!b) | (a,b) <- edges g]
          m1 = array (bounds g)  [(x,i) | (i,xs) <- zip [0..] q, x <- xs]
          m2 = array (bounds g') [(i,x) | (i,(x:_)) <- zip [0..] q]

classifyNode :: (Ord u) => Graph -> Tagging u -> [[Vertex]]
classifyNode g t = classify f (indices g)
    where rt    = reachabilityTable g t
          len   = rangeSize (bounds g)
          f n m = take len (rt!n) == take len (rt!m)

reachabilityTable :: (Ord u) => Graph -> Tagging u -> Table [[u]]
reachabilityTable g t = table
    where table = array (bounds g) [ (n, f n) | n <- indices g]
          f n = case g!n of
                []       -> [[t n]]
                children -> [] : merge (map (table!) children)
          merge = foldr (zipWith' unionSortedList) []

-----------------------------------------------------------------------------
-- utility functions
-----------------------------------------------------------------------------

classify :: (a -> a -> Bool) -> [a] -> [[a]]
classify f = foldl phi []
    where phi (s:ss) x | f (head s) x = (x:s) : ss
                       | otherwise    = s : phi ss x
          phi [] x = [[x]]

zipWith' :: (a -> a -> a) -> [a] -> [a] -> [a]
zipWith' f = g
    where g [] bs = bs
          g as [] = as
          g (a:as) (b:bs) = f a b : g as bs

unionSortedList :: (Ord a) => [a] -> [a] -> [a]
unionSortedList [] bs = bs
unionSortedList as [] = as
unionSortedList (a:as) (b:bs)
    = case a `compare` b of
      EQ -> a : unionSortedList as bs
      LT -> a : unionSortedList as (b:bs)
      GT -> b : unionSortedList (a:as) bs

-----------------------------------------------------------------------------
-- tests
-----------------------------------------------------------------------------

-- [[1,0]]
test1 = classifyNode g (undefined :: Tagging ())
    where g = buildG (0,1) [(0,1),(1,1)]

-- [[1,0],[2],[3]]
test2 = classifyNode g f
    where g = buildG (0,3) [(0,1),(1,1),(2,3)]
          f :: Vertex -> Maybe ()
          f _ = Nothing

-- [[3,0],[4,2,1]]
test3 = classifyNode g f
    where g = buildG (0,4) [(0,1),(0,2),(3,4)]
          f :: Vertex -> Maybe ()
          f _ = Nothing
