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

module Hyperset
    where

import Data.Graph
import Data.Array
import Data.Either
import Data.List (sort, nub, mapAccumL)
import qualified Data.List as List
import Data.FiniteMap
import Debug.Trace

-----------------------------------------------------------------------------

type Tagging u = FiniteMap Vertex u
type TaggedGraph u = (Graph, Tagging u)

{- invariant:
     (v `elem` keysFM (sysTagging sys)) => null (sysGraph sys ! v)
-}
data System u =
    System
    { sysGraph        :: !Graph
    , sysTagging      :: !(Tagging u)
    , sysReachability :: !(Table [[Maybe u]])
    , sysWellfounded  :: (Table Bool)
    }

instance (Ord u, Show u) => (Show (System u)) where
    showsPrec d System{ sysGraph = g, sysTagging = t}
        | d == 11   = ('(':) . f . (')':)
        | otherwise = f
        where f = ("System "++) . (showsPrec 11 g) . (' ':)
                  . (showsPrec 11 (fmToList t))

mkSystem :: Ord u => Graph -> Tagging u -> System u
mkSystem g t =
    System{ sysGraph        = g
          , sysTagging      = t'
          , sysReachability = reachabilityTable g t'
          , sysWellfounded  = wellfoundedTable g
          }
    where t' = filterFM (\v _ -> null (g!v)) t

-----------------------------------------------------------------------------

data Ord u => Set u = Set !(System u) !Vertex deriving Show

instance Ord u => Eq (Set u) where
    s1@(Set sys1 v1) == s2@(Set sys2 v2) =
        isWellfounded s1 == isWellfounded s2 &&
        take len (rt1!v1) == take len (rt2!v2)
        where rt1 = sysReachability sys1
              rt2 = sysReachability sys2
              len = max (rangeSize (bounds (sysGraph sys1)))
                        (rangeSize (bounds (sysGraph sys2)))

wrap :: Ord u => System u -> Vertex -> Either u (Set u)
wrap sys v = case lookupFM (sysTagging sys) v of
             Just e  -> Left e
             Nothing -> Right (Set sys v)

setToList :: Ord u => Set u -> [Either u (Set u)]
setToList (Set sys v) = map (wrap sys) (sysGraph sys ! v)

atom :: Ord u => Set u
atom = constructSet (array (0,0) [(0,[0])], emptyFM) [[[0]]] 0

emptySet :: Ord u => Set u
emptySet = mkSet []

mkSet :: Ord u => [Either u (Set u)] -> Set u
mkSet xs = constructSet (array (0,n) ((n,children):l), t) ([[n]]:qs) n
    where ((n,l,t,qs), children) = mapAccumL phi (0,[],emptyFM,[]) xs
          phi (n,l,t,qs) (Left u) =
              ((n+1, (n,[]):l, addToFM t n u, [[n]]:qs), n)
          phi (n,l,t,qs) (Right (Set sys v)) =
              ((ub+off+1, l'++l, addListToFM t t', q':qs), v+off)
              where (lb,ub) = bounds (sysGraph sys)
                    off = n - lb
                    l'  = [(v+off, [ch+off | ch <- children])
                           | (v,children) <- assocs (sysGraph sys)]
                    t'  = [(v+off,u) | (v,u) <- fmToList (sysTagging sys)]
                    q'  = [[i+off] | i <- indices (sysGraph sys)]

type Var = Int

solve :: Ord u => Array Var (Set (Either u Var)) -> Array Var (Set u)
solve equations = array (bounds equations)
                  [(i,x)
                   | i <- indices equations
                   , let Right x = wrap sys (m!i)]
    where (sys,m)  = normalize tg [ [[i]] | i <- indices g ]
          tg@(g,_) = mkTaggedGraphFromEquations equations

{-
solve (array (0,0) [(0,atom)])
=> array (0,0) [(0,Set (System (array (0,0) [(0,[0])]) []) 0)]

solve (array (0,1) [(0, mkSet [Left (Right 1)]), (1, mkSet [Left (Right 0)])])
=> array (0,1) [(0,Set (System (array (0,0) [(0,[0])]) []) 0),(1,Set (System (array (0,0) [(0,[0])]) []) 0)]
-}

-- XXX: ‰˜‚¢‚È‚Ÿ
mkTaggedGraphFromEquations
    :: Ord u => Array Var (Set (Either u Var)) -> TaggedGraph u
mkTaggedGraphFromEquations equations = (array (lb,ub') l, t)
    where (lb,ub) = bounds equations
          (ub',l,t) = foldl phi (ub,[],emptyFM) (assocs equations)
          phi (ub,l,t) (lhs, (Set sys v)) = (ub', l', t')
              where g = sysGraph sys
                    m = array (bounds g) m'
                    ((ub',l',t'), m') = mapAccumL psi (ub,l,t) (assocs g)
                        where psi (ub,l,t) (x,children)
                               | v==x =
                                   ( (ub, (lhs, map (m!) children) : l, t)
                                   , (x, lhs)
                                   )
                               | otherwise =
                                   case lookupFM (sysTagging sys) x of
                                   Just (Right v) ->
                                       ((ub,l,t), (x,v))
                                   Just (Left u) ->
                                       ( (ub+1
                                         , (ub+1,[]) : l
                                         , addToFM t (ub+1) u)
                                       , (x, ub+1)
                                       )
                                   Nothing ->
                                       ( ( ub+1
                                         , (ub+1, map (m!) children) : l
                                         , t
                                         )
                                       , (x, ub+1)
                                       )


singleton :: Ord u => Either u (Set u) -> Set u
singleton u = mkSet [u]

-- XXX: ‰˜‚¢‚È‚Ÿ
powerset :: Ord u => Set u -> Set u
powerset (Set sys v) = constructSet (g',t) qs v'
    where g = sysGraph sys
          t = sysTagging sys
          (lb,ub) = bounds g
          v'  = ub + 1
          ub' = v' + length p
          p   = zip [(v'+1)..] (powerList (g!v))
          g'  = array (lb, ub') ((v', [a | (a,_) <- p]) : p ++ assocs g)
          qs = ([[[i] | i <- indices g]] ++ [ [[i]] | i <- [ub+1..ub'] ])

-- XXX: ‰˜‚¢‚È‚Ÿ
union :: Ord u => Set u -> Set u -> Set u
union (Set sys1 v1) (Set sys2 v2) = constructSet (g,t) qs v
    where g1 = sysGraph sys1
          g2 = sysGraph sys2
          (lb1,ub1) = bounds g1
          (lb2,ub2) = bounds g2
          off = ub1 + 1 - lb2
          v = ub2+off+1
          g = array (lb1,v)
              ([(v, g1!v1 ++ map (off+) (g2!v2))] ++
               assocs g1 ++
               [(v+off, [ch+off| ch <- children])
                | (v,children) <- assocs g2])
          t = sysTagging sys1 `addListToFM`
              [(v+off,u) | (v,u) <- fmToList (sysTagging sys2)]
          qs = [[v]] : [[[i] | i <- indices g1], [[i+off] | i <- indices g2]]

intersect :: Ord u => Set u -> Set u -> Set u
a `intersect` b = separate (\x -> x `elementOf` b) a

minusSet :: Ord u => Set u -> Set u -> Set u
a `minusSet` b = separate (\x -> not (x `elementOf` b)) a

-- equiv_class

separate :: Ord u => (Either u (Set u) -> Bool) -> (Set u -> Set u)
separate f s@(Set sys@System{ sysGraph = g, sysTagging = t } v) =
    constructSet (g',t) qs v'
    where (lb,ub) = bounds g
          g'  = array (lb,ub+1) (foo : assocs g)
              where foo = (v', [child | child <- g!v, f (wrap sys child)])
          v'  = ub+1
          qs  = [[[v']]] ++ [[[i] | i <- indices g]]

mapSet :: (Ord u, Ord u') =>
          (Either u (Set u) -> Either u' (Set u')) -> (Set u -> Set u')
mapSet f = mkSet . map f . setToList

-----------------------------------------------------------------------------

elementOf :: Ord u => (Either u (Set u)) -> Set u -> Bool
elementOf x set = x `elem` setToList set

_subsetOf, subsetOf, supersetOf, properSubsetOf, properSupersetOf
    :: Ord u => Set u -> Set u -> Bool
as `_subsetOf`  bs = and [a `elementOf` bs | a <- setToList as]
as `subsetOf`   bs = cardinality as <= cardinality bs && as `_subsetOf` bs
as `supersetOf` bs = bs `subsetOf` as
as `properSubsetOf`   bs = cardinality as < cardinality bs && as `_subsetOf` bs
as `properSupersetOf` bs = bs `properSubsetOf` as

isWellfounded :: Ord u => Set u -> Bool
isWellfounded (Set sys v) = sysWellfounded sys ! v

cardinality :: Ord u => Set u -> Int
cardinality (Set sys v) = length (sysGraph sys ! v)

isEmptySet :: Ord u => Set u -> Bool
isEmptySet x = cardinality x == 0

isSingleton :: Ord u => Set u -> Bool
isSingleton x = cardinality x == 1

-----------------------------------------------------------------------------
{- FIXME: ˜AŒ‹¬•ª–ˆ‚ÉƒOƒ‰ƒt‚ð•ª‚¯‚éˆ—‚ð“ü‚ê‚é? -}

constructSet :: Ord u => TaggedGraph u -> [QuoSet Vertex] -> Vertex -> Set u
constructSet tg qs v = case wrap sys (m!v) of
                       Right set -> set
                       --Left _ -> error "shouldn't happen"
    where (sys, m) = normalize tg qs

normalize :: Ord u =>
             TaggedGraph u -> [QuoSet Vertex] -> (System u, Table Vertex)
normalize (g,t) qs = (mkSystem g' t', m)
    where g' = array (0, length c - 1)
                     [(i, sort $ nub $ [m!ch | ch <- g!x]) | (i,x:_) <- c]
          t' = listToFM [(m!v,u) | (v,u) <- fmToList t]
          m  = array (bounds g) [(x,i) | (i,xs) <- c, x <- xs]
          c  = zip [0..] (mergeQuoSets eq qs)
              where eq n m = take len (rt!n) == take len (rt!m)
                    rt     = reachabilityTable g t
                    len    = rangeSize (bounds g)

reachabilityTable :: Ord u => Graph -> Tagging u -> Table [[Maybe u]]
reachabilityTable g t = table
    where table = array (bounds g) [(n, f n) | n <- indices g]
          f n = case g!n of
                []       -> [lookupFM t n] : []
                children -> [] : merge (map (table!) children)
          merge = foldl (flip (zipWith' unionSortedList)) []

-----------------------------------------------------------------------------

wellfoundedTable :: Graph -> Table Bool
wellfoundedTable g = table
    where isCyclic = array (bounds g) (foldr phi [] scc)
              where phi (AcyclicSCC x) ys = (x,False) : ys
                    phi (CyclicSCC xs) ys = [(x,True) | x<-xs] ++ ys
                    scc = stronglyConnComp [(x,x,ys) | (x,ys) <- assocs g]
          table = array (bounds g) [(i, f i) | i <- indices g]
              where f n | isCyclic ! n = False
                        | otherwise    = foldr (&&) True (map (table!) (g!n))

-----------------------------------------------------------------------------
-- utility functions
-----------------------------------------------------------------------------

type EquivClass a = [a]
type QuoSet a = [EquivClass a]

mergeQuoSets :: (a -> a -> Bool) -> [QuoSet a] -> QuoSet a
mergeQuoSets eq = foldl (mergeQuoSet2 eq) []

mergeQuoSet2 :: (a -> a -> Bool) -> QuoSet a -> QuoSet a -> QuoSet a
mergeQuoSet2 eq = foldl phi
    where phi qa e1 = g qa
              where g [] = [e1]
                    g (e2:e2s) | r `eq` head e2 = (e1++e2) : e2s
                               | otherwise      = e2 : g e2s
                    r = head e1

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
