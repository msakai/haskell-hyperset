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
import Data.Either
import Data.List (find)
import Data.FiniteMap

data (Ord a) => Set a =
    Set{ apg     :: !APG
       , tagging :: !(Tagging a)
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
emptySet = Set (array (0,0) [(0,[])], 0) emptyFM

elementOf :: (Ord a) => (Either a (Set a)) -> Set a -> Bool
elementOf = either f g
    where f e (Set (g2,v2) t2) = any h (g2!v2)
              where h child = null (g2!child) &&
                              lookupFM t2 child == Just e -- XXX
          g (Set (g1,v1) t1) (Set (g2,v2) t2) = any h (g2!v2)
              where h child = foo == take len (rt2!child)
                    rt1 = reachabilityTable g1 t1
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
    case (construct g' t) ! n' of
    Right set -> set
    Left _    -> error "shouldn't happen"
    where (l,u) = bounds g
          n' = u + 1
          u' = u + 1 + length p
          p  = powerList (g!n)
          g' = array (l,u')
                     ((n',[(n'+1)..u']) : zip [(n'+1)..u'] p ++ assocs g)

-----------------------------------------------------------------------------

{- FIXME: �A���������ɃO���t�𕪂��� -}
construct :: (Ord a) => Graph -> Tagging a -> Table (Either a (Set a))
construct g t = array (bounds g) [(v, f g' t' (m!v)) | v <- indices g]
    where ((g',t'), m) = mkCanonicalPicture (g,t)
          f g t n = case g!n of
                    [] ->
                        case lookupFM t n of
                        Just e  -> Left e
                        Nothing -> Right (Set (g,n) t)
                    _  -> Right (Set (g,n) t)

mkCanonicalPicture
    :: (Ord u) => (Graph, Tagging u) -> ((Graph, Tagging u), Table Vertex)
mkCanonicalPicture (g,t) = ((g', t'), m)
    where g' = buildG (0, length q - 1) [(m!a, m!b) | (a,b) <- edges g]
          q  = zip [0..] (classifyNode g t)
          m  = array (bounds g)  [(x,i) | (i,xs) <- q, x <- xs]
          t' = listToFM [(m!k,v) | (k,v) <- fmToList t]

-----------------------------------------------------------------------------

classifyNode :: (Ord u) => Graph -> Tagging u -> [[Vertex]]
classifyNode g t = classify f (indices g)
    where rt    = reachabilityTable g t
          len   = rangeSize (bounds g)
          f n m = take len (rt!n) == take len (rt!m)

reachabilityTable :: (Ord u) => Graph -> Tagging u -> Table [[Maybe u]]
reachabilityTable g t = table
    where table = array (bounds g) [(n, f n) | n <- indices g]
          f n = case g!n of
                []       -> [lookupFM t n] : []
                children -> [] : merge (map (table!) children)
          merge = foldr (zipWith' unionSortedList) []

-----------------------------------------------------------------------------

height :: Graph -> Table (Maybe Int)
height g = table
    where scc = stronglyConnComp [(x,x,ys) | (x,ys) <- assocs g]
          isCyclic = array (bounds g) (foldr phi [] scc)
              where phi (AcyclicSCC x) ys = (x,False) : ys
                    phi (CyclicSCC xs) ys = [(x,True) | x<-xs] ++ ys
          table = array (bounds g) [(i, f i) | i <- indices g]
              where f n | isCyclic!n = Nothing
                        | otherwise =
                            foldr phi (Just 0) (map (table!) (g!n))
                    phi Nothing _ = Nothing
                    phi _ Nothing = Nothing
                    phi (Just m) (Just n) = Just (max (m+1) n) -- XXX

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

test4 = height (array (0,4) [(0,[0]), (1,[2,3]), (2,[]), (3,[2]), (4,[0])])