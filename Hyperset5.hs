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
import Data.Either
import Data.List (find)
import Data.FiniteMap

-----------------------------------------------------------------------------

type Tagging u = FiniteMap Vertex u

{- invariant:
     (v `elem` keysFM (sysTagging sys)) => null (sysGraph sys ! v)
-}
data System u =
    System
    { sysGraph        :: !Graph
    , sysTagging      :: !(Tagging u)
    , sysReachability :: !(Table [[Maybe u]])
    }

mkSystem :: Ord u => Graph -> Tagging u -> System u
mkSystem g t =
    System{ sysGraph        = g
          , sysTagging      = t'
          , sysReachability = reachabilityTable g t'
          }
    where t' = listToFM [p | p@(v,_) <- (fmToList t), null (g!v)]

-----------------------------------------------------------------------------

data Ord u => Set u = Set !(System u) !Vertex

instance Ord u => Eq (Set u) where
    (Set sys1 v1) == (Set sys2 v2) =
        take len (rt1!v1) == take len (rt2!v2)
        where rt1 = sysReachability sys1
              rt2 = sysReachability sys2
              len = max (rangeSize (bounds (sysGraph sys1)))
                        (rangeSize (bounds (sysGraph sys2)))

wrap :: Ord u => System u -> Vertex -> Either u (Set u)
wrap sys v = case lookupFM (sysTagging sys) v of
             Just e  -> Left e
             Nothing -> Right (Set sys v)

emptySet :: Ord u => Set u
emptySet = case hoge!0 of Right set -> set
    where hoge = construct (array (0,0) [(0,[])]) emptyFM

atom :: Ord u => Set u
atom = case construct (array (0,0) [(0,[0])]) emptyFM ! 0 of
       Right set -> set

-- mkSet :: Ord a => [Either u (Set u)] -> Set a

setToList :: Ord u => Set u -> [Either u (Set u)]
setToList (Set sys v) = map (wrap sys) (sysGraph sys ! v)

{-
unitSet :: Ord u => Either u (Set u) -> Set u
unitSet u =
    
-}

-- XXX: ‰˜‚¢‚È‚Ÿ
powerset :: Ord u => Set u -> Set u
powerset (Set sys v) = case construct g' (sysTagging sys) ! v' of
                       Right set -> set
    where g = sysGraph sys
          (l,u) = bounds g
          v' = u + 1
          p  = zip [(v'+1)..] (powerList (g!v))
          g' = array (l, v' + length p)
                     ([(v', [a | (a,_) <- p])] ++ p ++ assocs g))

elementOf :: Ord u => (Either u (Set u)) -> Set u -> Bool
elementOf = either elementOf1 elementOf2

elementOf1 :: Ord u => u -> Set u -> Bool
elementOf1 e (Set sys v) = any f (sysGraph sys ! v)
    where f child = lookupFM (sysTagging sys) child == Just e

elementOf2 :: Ord u => Set u -> Set u -> Bool
elementOf2 (Set sys1 v1) (Set sys2 v2) = any f (g2!v2)
    where f child = take len (rt1!v1) == take len (rt2!child)
          g1  = sysGraph sys1
          g2  = sysGraph sys2
          rt1 = sysReachability sys1
          rt2 = sysReachability sys2
          len = max (rangeSize (bounds g1)) (rangeSize (bounds g2))

-- isWellfounded :: Ord u => Set u -> Bool

isEmptySet :: Ord u => Set u -> Bool
isEmptySet x = cardinality x == 0

cardinality :: Ord u => Set u -> Int
cardinality (Set sys v) = length (sysGraph sys ! v)

-----------------------------------------------------------------------------

{- FIXME: ˜AŒ‹¬•ª–ˆ‚ÉƒOƒ‰ƒt‚ð•ª‚¯‚é? -}
construct :: Ord u => Graph -> Tagging u -> Table (Either u (Set u))
construct g t = array (bounds g) [(v, wrap sys (m!v)) | v <- indices g]
    where ((g',t'), m) = mkCanonicalPicture (g,t)
          sys = mkSystem g' t'

type TaggedGraph u = (Graph, Tagging u)

mkCanonicalPicture :: Ord u => TaggedGraph u -> (TaggedGraph u, Table Vertex)
mkCanonicalPicture (g,t) = ((g',t'), m)
    where g' = buildG (0, length c - 1) [(m!a, m!b) | (a,b) <- edges g]
          c  = zip [0..] (classifyNode g t)
          m  = array (bounds g) [(x,i) | (i,xs) <- c, x <- xs]
          t' = listToFM [(m!k,v) | (k,v) <- fmToList t]

-----------------------------------------------------------------------------

classifyNode :: Ord u => Graph -> Tagging u -> [[Vertex]]
classifyNode g t = classify f (indices g)
    where rt    = reachabilityTable g t
          len   = rangeSize (bounds g)
          f n m = take len (rt!n) == take len (rt!m)

reachabilityTable :: Ord u => Graph -> Tagging u -> Table [[Maybe u]]
reachabilityTable g t = table
    where table = array (bounds g) [(n, f n) | n <- indices g]
          f n = case g!n of
                []       -> [lookupFM t n] : []
                children -> [] : merge (map (table!) children)
          merge = foldr (zipWith' unionSortedList) []

-----------------------------------------------------------------------------

heightTable :: Graph -> Table (Maybe Int)
heightTable g = table
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
test1 = classifyNode g (emptyFM :: Tagging ())
    where g = buildG (0,1) [(0,1),(1,1)]

-- [[1,0],[2],[3]]
test2 = classifyNode g t
    where g = buildG (0,3) [(0,1),(1,1),(2,3)]
          t = listToFM [(3,())]

-- [[3,0],[4,2,1]]
test3 = classifyNode g t
    where g = buildG (0,4) [(0,1),(0,2),(3,4)]
          t = listToFM [(1,()),(2,()),(4,())]

test4 = heightTable (array (0,4) [(0,[0]), (1,[2,3]), (2,[]), (3,[2]), (4,[0])])