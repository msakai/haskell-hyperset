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
import Data.Maybe (isJust, fromJust)
import Data.List (find)
import Data.FiniteMap

data (Ord a) => Set a =
    Set{ apg     :: !APG
       , tagging :: !(Tagging (Maybe a))
       }

type APG = (Graph,Vertex)
type Tagging u = FiniteMap Vertex u

-----------------------------------------------------------------------------

instance (Ord a) => Eq (Set a) where
    (Set (g1,v1) t1) == (Set (g2,v2) t2) =
        take len (rt1!v1) == take len (rt2!v2)
        where rt1 = reachabilityTable g1 t1
              rt2 = reachabilityTable g2 t2
              len = max (rangeSize (bounds g1)) (rangeSize (bounds g2))

-- emptySet :: Set a
-- mkSet :: Ord a => [a] -> Set a
-- setToList :: Set a -> [a]
-- unitSet :: a -> Set a

emptySet :: (Ord a) => Set a
emptySet = Set (array (0,0) [(0,[])], 0) (listToFM [(0,Nothing)])

elementOf :: (Ord a) => (Either a (Set a)) -> Set a -> Bool
--elementOf (Left e) (Set (g2,v2) t2) =
--    elementOf 
elementOf (Right (Set (g1,v1) t1)) (Set (g2,v2) t2) =
    any (\child -> foo == take len (rt2!child)) (g2!v2)
    where rt1 = reachabilityTable g1 t1
          rt2 = reachabilityTable g2 t2
          len = max (rangeSize (bounds g1)) (rangeSize (bounds g2))
          foo = take len (rt1!v1)

isEmptySet :: (Ord a) => Set a -> Bool
isEmptySet x = cardinality x == 0

cardinality :: (Ord a) => Set a -> Int
cardinality (Set (g1,v1) t1) = length (g1!v1)

-- XXX
powerset :: (Ord a) => Set a -> Set a
powerset (Set (g,n) t) =
    case (construct g' t') ! n' of
    Right set -> set
    Left _    -> error "shouldn't happen"
    where (l,u) = bounds g
          n' = u + 1
          u' = u + 1 + length p
          p  = powerList (g!n)
          t' = t `plusFM` listToFM [ (parent, Nothing)
                                   | (parent, children) <- zip [(n'+1)..u'] p
                                   , null children]
          g' = array (l,u')
                     ((n',[(n'+1)..u']) : zip [(n'+1)..u'] p ++ assocs g)

-----------------------------------------------------------------------------

{- FIXME: 連結成分毎にグラフを分ける -}
construct :: (Ord a) => Graph -> Tagging (Maybe a) -> Table (Either a (Set a))
construct g t = array (bounds g) [(v, f g' t' (m1!v)) | v <- indices g]
    where (g', m1, m2) = mkCanonicalPicture g t
          t' = listToFM [ (v', fromJust (lookupFM t (m2!v')))
                        | v' <- indices g']

	  f g t n =
	      case g!n of
              [] ->
                  case fromJust (lookupFM t n) of
                  Just e  -> Left e
                  Nothing -> Right (Set (g,n) t)
              _  -> Right (Set (g,n) t)

{- FIXME: 返り値の型を整理する -}
mkCanonicalPicture ::
    (Ord u) => Graph -> Tagging u ->
    ( Graph        -- new graph
    , Table Vertex -- vertex mapping from old graph to new graph
    , Table Vertex -- vertex mapping from new graph to old graph
    )
mkCanonicalPicture g t = (g',m1,m2)
    where q  = zip [0..] (classifyNode g t)
          g' = buildG (0, length q - 1) [(m1!a,m1!b) | (a,b) <- edges g]
          m1 = array (bounds g)  [(x,i) | (i,xs) <- q, x <- xs]
          m2 = array (bounds g') [(i,x) | (i,(x:_)) <- q]

-----------------------------------------------------------------------------

classifyNode :: (Ord u) => Graph -> Tagging u -> [[Vertex]]
classifyNode g t = classify f (indices g)
    where rt    = reachabilityTable g t
          len   = rangeSize (bounds g)
          f n m = take len (rt!n) == take len (rt!m)

reachabilityTable :: (Ord u) => Graph -> Tagging u -> Table [[u]]
reachabilityTable g t = table
    where table = array (bounds g) [(n, f n) | n <- indices g]
          f n = case g!n of
                []       -> [fromJust (lookupFM t n)] : []
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

powerList :: [a] -> [[a]]
powerList = foldr phi [[]]
    where phi a xs = map (a:) xs ++ xs

-----------------------------------------------------------------------------
-- tests
-----------------------------------------------------------------------------

-- [[1,0]]
test1 = classifyNode g (undefined :: Tagging ())
    where g = buildG (0,1) [(0,1),(1,1)]

-- [[1,0],[2],[3]]
test2 = classifyNode g t
    where g = buildG (0,3) [(0,1),(1,1),(2,3)]
	  t = listToFM [(3,())]

-- [[3,0],[4,2,1]]
test3 = classifyNode g t
    where g = buildG (0,4) [(0,1),(0,2),(3,4)]
	  t = listToFM [(1,()),(2,()),(4,())]


{-
height :: Graph -> Table (Maybe Int)
height g = table
    where scc = stronglyConnComp [(x,x,ys) | (x,ys) <- assocs g]
          cyclicNodes = foldr phi [] scc
              where phi (AcyclicSCC _) ys = xs
                    phi (CyclicSCC xs) ys = xs ++ ys
          table = array (bounds g) [(i, f i) | i <- indices g]
              where f x = if x `elem` cyclicNodes
                          then Nothing
                          else
-}
                          

--test4 =
--    scc (array (0,1) [(0,[0]),(1,[])])