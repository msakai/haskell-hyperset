-----------------------------------------------------------------------------
-- |
-- Module      :  Hyperset
-- Copyright   :  (c) Masahiro Sakai 2004,2005
-- License     :  BSD-style
-- 
-- Maintainer  :  sakai@tom.sfc.keio.ac.jp
-- Stability   :  unstable
-- Portability :  portable
--
-- An implementation of hypersets.
--
-----------------------------------------------------------------------------

module Hyperset
    (
    -- * The @Set@ type
      Set
    , Elem (..)

    -- * Operators
    , (\\)

    -- * Inspection
    , isWellfounded
    , cardinality
    , isEmpty
    , isSingleton
    , member
    , subset
    , superset
    , properSubset
    , properSuperset

    -- * Construction
    , quineAtom
    , empty
    , singleton
    , powerset
    , union
    , intersection
    , difference
    , equivClass
    , separate

    -- * System of equations
    , SystemOfEquations
    , Var
    , Solution
    , solve

    -- * Accessible Graph.
    , Tagging
    , Decoration
    , decorate
    , picture

    -- * Conversion

    -- ** List
    , elems
    , toList
    , fromList

    -- , mapSet
    ) where

import Data.Graph (Graph,Vertex,Table)
import qualified Data.Graph as Graph (scc)
import Data.Tree (Tree)
import qualified Data.Tree as Tree (flatten)
import Data.Array.IArray hiding (elems)
import qualified Data.Array.IArray as IArray
import Data.Array.ST
import Data.FiniteMap
import Data.List (mapAccumL)
import Data.STRef
import Control.Monad (unless, foldM, mapM_, mapM)
import Control.Monad.ST (runST, ST)
import qualified IntSet as IS

{--------------------------------------------------------------------
  Operators
--------------------------------------------------------------------}
infixl 9 \\

-- | See 'difference'.
(\\) :: Ord u => Set u -> Set u -> Set u
s1 \\ s2 = s1 `difference` s2

{--------------------------------------------------------------------
  Set type
--------------------------------------------------------------------}

-- |Set with urelemente from @u@.
data Ord u => Set u = Set !(System u) !Vertex

-- |Urelemnt or set.
data Ord u => Elem u
    = SetElem (Set u)
    | Urelem u

--type UrelemOrSet u = Either u (Set u)

instance Ord u => Eq (Set u) where
    s1 == s2 | isEmpty s1 && isEmpty s2 = True
    s1@(Set sys1 v1) == s2@(Set sys2 v2) =
        sysAttrTable sys1 ! v1 == sysAttrTable sys2 ! v2 &&
        cardinality s1 == cardinality s2 &&
        in1!v1 == in2!v2
        where (_,in1,in2) = mergeSystem sys1 sys2

-- for debugging
instance (Ord u, Show u) => Show (Set u) where
    showsPrec d s = showsPrec d (g, v, fmToList t)
       where (g,v,t) = picture s

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- |Is this a well-founded set?
isWellfounded :: Ord u => Set u -> Bool
isWellfounded (Set sys v) =
    case (sysAttrTable sys ! v) of
    (wf,_) -> wf

-- |The number of elements in the set.
cardinality :: Ord u => Set u -> Int
cardinality (Set sys v) = length (sysGraph sys ! v)

-- |Is this the empty set?
isEmpty :: Ord u => Set u -> Bool
isEmpty x = cardinality x == 0

-- |Is this a singleton set?.
isSingleton :: Ord u => Set u -> Bool
isSingleton x = cardinality x == 1

-- XXX: 汚いなぁ
-- |Is the element in the set?
member :: Ord u => Elem u -> Set u -> Bool
member (Urelem x) (Set sys v) =
    any (\y -> lookupFM t y == Just x) (g!v)
    where t = sysTagging sys
          g = sysGraph sys
member (SetElem s1) (Set sys v) | isEmpty s1 =
    any (\y -> null (g!y) && lookupFM t y == Nothing) (g!v)    
    where t = sysTagging sys
          g = sysGraph sys
member (SetElem (Set sys1 v1)) (Set sys2 v2) =
    (in1 ! v1) `elem` (g ! (in2 ! v2))
    where (sys,in1,in2) = mergeSystem sys1 sys2
          g = sysGraph sys

_subset :: Ord u => Set u -> Set u -> Bool
s `_subset` _ | isEmpty s = True
(Set sys1 v1) `_subset` (Set sys2 v2) = xs `IS.subset` ys
    where g1 = sysGraph sys1
          g2 = sysGraph sys2
          (_,in1,in2) = mergeSystem sys1 sys2
          xs = IS.fromList (map (in1!) (g1 ! v1))
          ys = IS.fromList (map (in2!) (g2 ! v2))

-- |Is this a subset?
-- @(s1 \`subset\` s2)@ tells whether s1 is a subset of s2.
subset :: Ord u => Set u -> Set u -> Bool
as `subset` bs = cardinality as <= cardinality bs && as `_subset` bs

-- |Is this superset?
-- @(s1 \`superset\` s2)@ tells whether s1 is a superset of s2.
superset :: Ord u => Set u -> Set u -> Bool
as `superset` bs = bs `subset` as

-- |Is this a proper subset?
-- @(s1 \`properSubset\` s2)@ tells whether s1 is a proper subset of s2.
properSubset :: Ord u => Set u -> Set u -> Bool
as `properSubset` bs = cardinality as < cardinality bs && as `_subset` bs

-- |Is this a proper subset?
-- @(s1 \`properSuperset\` s2)@ tells whether s1 is a proper superset of s2.
properSuperset :: Ord u => Set u -> Set u -> Bool
as `properSuperset` bs = bs `properSubset` as

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- |Quine atom: x={x}.
quineAtom :: Ord u => Set u
quineAtom = constructSet2 ( listArray (0,0) [[0]]
                          , emptyFM
                          , listArray (0,0) [(False,RankNegInf)]
                          ) 0

-- |The empty set.
empty :: Ord u => Set u
empty = fromList []

-- |Create a singleton set.
singleton :: Ord u => Elem u -> Set u
singleton u = fromList [u]

-- XXX: 汚いなぁ
-- |The powerset of the set.
powerset :: Ord u => Set u -> Set u
powerset (Set sys v) = constructSet2 (g',t,attrs') v'
    where g = sysGraph sys
          t = sysTagging sys
          attrs = sysAttrTable sys
          (lb,ub) = bounds g
          v' = ub + length p + 1
          p  = zip [(ub+1)..] (powerList (g!v))
          g' = array (lb, v') ((v', map fst p) : p ++ assocs g)
          attrs' = array (lb, v') $
                     (v', attrOfSetFromElemAttrs (map ((attrs'!) . fst) p)) :
                     [(i, attrOfSetFromElemAttrs (map (attrs!) children))
                     | (i,children) <- p ]
                     ++ assocs attrs

-- Mark Jones' powerSet
-- http://www.haskell.org/pipermail/haskell-cafe/2003-June/004484.html
powerList :: [a] -> [[a]]
powerList = foldr phi [[]]
    where phi x xs = xs /\/ map (x:) xs
          []     /\/ ys = ys
          (x:xs) /\/ ys = x : (ys /\/ xs)

-- XXX: 汚いなぁ
-- |The union of two sets.
union :: Ord u => Set u -> Set u -> Set u
union (Set sys1 v1) (Set sys2 v2) = constructSet2 (g,t,a) v
    where g1 = sysGraph sys1
          g2 = sysGraph sys2
          (lb1,ub1) = bounds g1
          (lb2,ub2) = bounds g2
          off = ub1 + 1 - lb2
          v = ub2+off+1
          g = array (lb1,v) l
              where l = [(v, g1!v1 ++ map (off+) (g2!v2))] ++
                        assocs g1 ++
                        [(v+off, map (off+) children)
                         | (v,children) <- assocs g2]
          t = t1 `addListToFM` [(v+off,u) | (v,u) <- fmToList t2]
              where t1 = sysTagging sys1
                    t2 = sysTagging sys2
          a = array (lb1,v) l
              where l = (v, attrOfSetFromElemAttrs (map (attrs1!) (g1!v1) ++ map (attrs2!) (g2!v2))) : [(i+off, a) | (i,a) <- assocs attrs2] ++ assocs attrs1
                    attrs1 = sysAttrTable sys1
                    attrs2 = sysAttrTable sys2

-- unionManySets :: Ord u => Set u -> Set u

-- 効率が悪い
-- |The intersection of two sets.
intersection :: Ord u => Set u -> Set u -> Set u
a `intersection` b = separate (\x -> x `member` b) a

-- 効率が悪い
-- |The difference of two sets.
difference :: Ord u => Set u -> Set u -> Set u
a `difference` b = separate (\x -> not (x `member` b)) a

-- |The quotient set by the equivalent relation.
equivClass :: Ord u => (Elem u -> Elem u -> Bool) -> (Set u -> Set u)
equivClass f (Set sys v) = constructSet2 (g', sysTagging sys, a) v'
    where f' a b = f (toElem sys a) (toElem sys b)
          g = sysGraph sys
          l = zip [ub+1..] (classifyList f' (g ! v))
          (lb,ub) = bounds (sysGraph sys)
          v' = ub + length l + 1
          g' = array (lb, v') ((v', map fst l) : l ++ assocs g)
          a  = array (lb, v') $
                 (v', attrOfSetFromElemAttrs [a!i | (i,_) <- l]) :
                 [(i, attrOfSetFromElemAttrs [attrs!ch | ch <- children])
                  | (i,children) <- l] ++ assocs attrs
              where attrs = sysAttrTable sys

classifyList :: (a -> a -> Bool) -> [a] -> [[a]]
classifyList f = foldl phi []
    where phi (s:ss) x | f (head s) x = (x:s) : ss
                       | otherwise    = s : phi ss x
          phi [] x = [[x]]

-- |Filter all elements that satisfy the predicate.
separate :: Ord u => (Elem u -> Bool) -> (Set u -> Set u)
separate f (Set sys v) = constructSet2 (g',t,a') v'
    where g = sysGraph sys
          t = sysTagging sys
          a = sysAttrTable sys
          (lb,ub) = bounds g
          g' = array (lb,ub+1) ((v', children) : assocs g)
          children = [ch | ch <- g!v, f (toElem sys ch)]
          v' = ub+1
          a' = array (lb,ub+1)
                 ((v', attrOfSetFromElemAttrs (map (a!) children)) : assocs a)

-- partition :: Ord u => (Elem u -> Bool) -> Set u -> (Set u, Set u)

toElem :: Ord u => System u -> Vertex -> Elem u
toElem sys v = case lookupFM (sysTagging sys) v of
               Just e  -> Urelem e
               Nothing -> SetElem (Set sys v)

{-
constructSet :: Ord u => TaggedGraph u -> Vertex -> Set u
constructSet (g,t) v = constructSet2 (g,t,attrTable g) v
-}

constructSet2 :: Ord u => TAGraph u -> Vertex -> Set u
constructSet2 g v = Set sys (m!v)
    where (sys,m) = mkSystem2 g

{--------------------------------------------------------------------
  System of equation
--------------------------------------------------------------------}

-- |System of equations in X is a family of equations
-- {x = a_x | x∈X}, exactly one equation for each indeterminant
-- x∈X⊆'Var'.
type SystemOfEquations u = Array Var (Set (Either u Var))

-- |Indeterminant in system of equation.
type Var = Int

-- |Solution of system of equation.
type Solution u = Array Var (Set u)

-- |Solve a system of equation.
-- By the solution lemma, every system of equations has a unique solution.
solve :: Ord u => SystemOfEquations u -> Solution u
solve equations = listArray (bounds equations)
                  [Set sys (m!i) | i <- indices equations]
    where (sys,m) = mkSystem $ mkTaggedGraphFromEquations equations

-- XXX: 汚いなぁ
mkTaggedGraphFromEquations :: Ord u => SystemOfEquations u -> TaggedGraph u
mkTaggedGraphFromEquations equations = (array (lb,ub') l, t)
    where (lb,ub) = bounds equations
          (ub',l,t) = foldl phi (ub,[],emptyFM) (assocs equations)
          phi (ub,l,t) (lhs, (Set sys v)) = (ub', l', t')
              where g = sysGraph sys
                    m :: Array Var Vertex
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

{--------------------------------------------------------------------
  Accessible Graph
--------------------------------------------------------------------}

-- |Let G be an accessible graph, and let U={φ}∪@u@ be a collection
-- containing the empty set and urelemente. A tagging of G is a function
-- t: G->U that assigns to each childless node of G an element of U.
-- For a childless node v of G, we interpret @lookupFM t v == Just u@
-- as t(v)=u, @lookupFM t v == Just u@ as t(v)=φ.
type Tagging u = FiniteMap Vertex u

-- |A decoration is a function d defined on each node n of G such that
--
-- * d(n) = t(n) (if n is childless) 
--
-- * d(n) = {d(m) | m∈children(n)}
--
type Decoration u = Table (Elem u)

-- |compute the decoration.
decorate :: Ord u => Graph -> Tagging u -> Decoration u
decorate g t = d
    where (sys,m) = mkSystem (g,t)
          d = listArray (bounds g) [toElem sys (m!v) | v <- indices g]

-- |Tagged apg(accessible pointed graph) that pictures the set.
picture :: Ord u => Set u -> (Graph, Vertex, Tagging u)
picture (Set sys v) = (sysGraph sys, v, sysTagging sys)

{--------------------------------------------------------------------
  Conversion
--------------------------------------------------------------------}

-- |The elements of a set.
elems :: Ord u => Set u -> [Elem u]
elems s = toList s

-- |The elements of a set.
toList :: Ord u => Set u -> [Elem u]
toList (Set sys v) = map (toElem sys) (sysGraph sys ! v)

-- |Create a set from a list of elements.
fromList :: Ord u => [Elem u] -> Set u
fromList xs = constructSet2 ( array (0,n) ((n, children) : l)
                            , t
                            , array (0,n) ((n, attrOfSetFromElems xs) : a)
                            ) n
    where ((n,l,t,a), children) = mapAccumL phi (0,[],emptyFM,[]) xs
          phi (n,l,t,a) (Urelem u) =
              ( (n+1, (n,[]):l, addToFM t n u, (n, (True,Rank 0)) : a)
              , n
              )
          phi (n,l,t,a) (SetElem (Set sys v)) =
              ( (ub+off+1, l'++l, addListToFM t t', a')
              , v+off
              )
              where (lb,ub) = bounds (sysGraph sys)
                    off = n - lb
                    l'  = [(v+off, [ch+off | ch <- children])
                           | (v,children) <- assocs (sysGraph sys)]
                    t'  = [(v+off,u) | (v,u) <- fmToList (sysTagging sys)]
                    a'  = [(i+off,x) | (i,x) <- assocs (sysAttrTable sys)]
                          ++ a

{--------------------------------------------------------------------
  Implementation
--------------------------------------------------------------------}

type TaggedGraph u = (Graph, Tagging u)

-- type AGraph u = Array Int (IS.IntSet, Attr)

data System u =
    System
    { sysGraph        :: !Graph
    , sysTagging      :: !(Tagging u)
    , sysAttrTable    :: Table Attr
    }

mkSystem :: Ord u => TaggedGraph u -> (System u, Table Vertex)
mkSystem (g,t) = (sys, m)
    where ((g',t'),attrs,m) = minimize (g,t)
          sys = System
                { sysGraph      = g'
                , sysTagging    = filterFM (\v _ -> null (g' ! v)) t'
                , sysAttrTable  = attrs
                }

mkSystem2 :: Ord u => TAGraph u -> (System u, Table Vertex)
mkSystem2 g = (sys, m)
    where ((g',t',attrs), m) = minimizeTAGraph g
          sys = System
                { sysGraph      = g'
                , sysTagging    = filterFM (\v _ -> null (g' ! v)) t'
                , sysAttrTable  = attrs
                }

mergeSystem :: Ord u => System u -> System u ->
               (System u, Table Vertex, Table Vertex)
mergeSystem sys1 sys2 = (sys, in1, in2)
    where g1 = sysGraph sys1
          g2 = sysGraph sys2
          (offset, lb, ub) = (ub1 + 1 - lb2, lb1, ub2+offset)
              where (lb1,ub1) = bounds g1
                    (lb2,ub2) = bounds g2
          in1 = listArray (bounds g1) [m!i | i <- indices g1]
          in2 = listArray (bounds g2) [m!(i+offset) | i <- indices g2]
          (sys,m) = mkSystem (g,t)
              where g = array (lb,ub) (assocs g1 ++ [(k+offset, map (offset+) e) | (k,e) <- assocs g2])
                    t = t1 `plusFM` t2
                        where t1 = sysTagging sys1
                              t2 = listToFM [(k+offset,e) | (k,e) <- fmToList (sysTagging sys2)]

-----------------------------------------------------------------------------

type Attr =
    ( Bool -- wellfounededness
    , Rank -- Rank
    )

data Rank
    = RankNegInf -- -∞
    | Rank !Int
    deriving (Eq,Show,Read)

instance Ord Rank where
    Rank m `compare` Rank n = m `compare` n
    RankNegInf `compare` RankNegInf = EQ
    RankNegInf `compare` _ = LT
    _ `compare` RankNegInf = GT

{-# INLINE succRank #-}
succRank :: Rank -> Rank
succRank (Rank n)   = Rank (n+1)
succRank RankNegInf = RankNegInf

attrTable :: Graph -> Table Attr
attrTable g = table
    where table = array (bounds g)
                  [(x,(wf,rank)) | (xs,wf,rank) <- sccInfo, x <- IS.toList xs]
          gS = fmap IS.fromList g
          sccInfo :: [(IS.IntSet, Bool, Rank)]
          sccInfo = map f (Graph.scc g)
          f :: Tree Vertex -> (IS.IntSet, Bool, Rank)
          f sccT = (sccS, wf, rank)
              where sccL = Tree.flatten sccT
                    sccS = IS.fromList sccL
                    wf = case sccL of
                         [x] | x `IS.member` (gS!x) -> False
                             | otherwise  ->
                                 and [wf | ch <- g!x, let (wf,_) = table!ch]
                         _ -> False
                    rank = case sccL of
                           [x] | null (g!x) -> Rank 0
                           _   | IS.isEmpty children -> RankNegInf
                               | otherwise ->
                                   maximum
                                   [ if wf then succRank r else r
                                   | ch <- IS.toList children
                                   , let (wf,r) = table ! ch
                                   ]
                    children = IS.unions (map (gS!) sccL) `IS.difference` sccS


attrOfElem :: Ord u => Elem u -> Attr
attrOfElem (Urelem _) = (True, Rank 0)
attrOfElem (SetElem (Set sys v)) = sysAttrTable sys ! v

attrOfSetFromElems :: Ord u => [Elem u] -> Attr
attrOfSetFromElems = attrOfSetFromElemAttrs . map attrOfElem

-- 要素のAttrから集合のAttrを計算
attrOfSetFromElemAttrs :: [Attr] -> Attr
attrOfSetFromElemAttrs [] = (True, Rank 0)
attrOfSetFromElemAttrs xs = foldl phi (True,RankNegInf) xs
    where phi (wf,rank) a = case f a of
                            (wf1,rank1) -> (wf && wf1, rank `max` rank1)
          f (True,rank)  = (True,  succRank rank)
          f (False,rank) = (False, rank)

-----------------------------------------------------------------------------

type Block = IS.IntSet
type Partition = [Block]

type CellInfo =
    ( FiniteMap Rank IS.IntSet
    , IS.IntSet
    , Attr
    )

{-
data Cell
    = Redirect !Vertex
    | Cell !CellInfo
-}

type CollapsingTable      = Array Vertex (Either Vertex CellInfo)
type STCollapsingTable st = STArray st Vertex (Either Vertex CellInfo)

type PreimageMap = FiniteMap Rank IS.IntSet

mkSTCollapsingTable :: Graph -> Table Attr -> ST st (STCollapsingTable st)
mkSTCollapsingTable g table =
    do t <- mkPreimageTable g table >>= unsafeFreeze
       let t_ :: Array Vertex PreimageMap
           t_ = t
       newListArray (bounds g) [ Right (t!v, IS.single v, table!v)
                               | v <- indices g ]

mkPreimageTable :: Graph -> Table Attr -> ST st (STArray st Vertex PreimageMap)
mkPreimageTable g t =
    do table <- newListArray (bounds g) (repeat emptyFM)
       flip mapM_ (assocs g) $ \(v,children) ->
            do let (wf,rank) = t!v
                   v' = IS.single v
               flip mapM_ children $ \ch ->
                   do fm <- readArray table ch
                      let fm' = addToFM_C IS.union fm rank v'
                      writeArray table ch fm'
       return table

getNodeInfo :: STCollapsingTable st -> Vertex -> ST st (Vertex, FiniteMap Rank IS.IntSet, IS.IntSet, Attr)
getNodeInfo g x =
    do y <- readArray g x
       case y of
          Right (parents,vs,attr) -> return (x,parents,vs,attr)
          Left y1 -> getNodeInfo g y1

getParents :: STCollapsingTable st -> Vertex -> ST st (FiniteMap Rank IS.IntSet)
getParents g v =
    do (_,parents,_,_) <- getNodeInfo g v
       return parents

collapse :: STCollapsingTable st -> Vertex -> Vertex -> ST st Vertex
collapse g a' b' =
    do (a,pas,as,attr) <- getNodeInfo g a'
       (b,pbs,bs,_)    <- getNodeInfo g b'
       if a==b
          then return a
          else do writeArray g a $ Right ( plusFM_C IS.union pas pbs
                                         , as  `IS.union` bs
                                         , attr
                                         )
                  let redirect = Left a
                  mapM_ (\b -> writeArray g b redirect) (IS.toList bs)
                  return a

collapseList :: STCollapsingTable st -> [Vertex] -> ST st Vertex
collapseList _ []     = return undefined
collapseList g (x:xs) = foldM (collapse g) x xs

collapseBlock :: STCollapsingTable st -> Block -> ST st Vertex
collapseBlock g b = collapseList g (IS.toList b)

-----------------------------------------------------------------------------

refine :: STCollapsingTable st -> [(Rank, (STRef st Partition, Block))] -> Vertex -> ST st ()
refine g p v =
    do parents <- getParents g v
       unless (isEmptyFM parents) $
           flip mapM_ p $ \(rank, (ref,bi)) ->
                case lookupFM parents rank of
                Just xs -> modifySTRef ref (split xs)
                Nothing -> return ()

split :: IS.IntSet -> Partition -> Partition
split splitter xs = foldr phi [] xs
    where phi x ys = case splitIntSet splitter x of
                     Just (a,b) -> a : b : ys
                     Nothing    -> x : ys

-----------------------------------------------------------------------------

minimize :: Ord u => TaggedGraph u -> (TaggedGraph u, Table Attr, Table Vertex)
minimize (g,t) = ((g',t'), attrs', f)
    where ((g',t',attrs'), f) = minimizeTAGraph (g,t,attrs)
          attrs = attrTable g

type TAGraph u = (Graph, Tagging u, Table Attr)

minimizeTAGraph :: Ord u => TAGraph u -> (TAGraph u, Table Vertex)
minimizeTAGraph (g,t,attrs) = ((g',t',attrs'), f)
    where t' = listToFM [(f!v,u) | (v,u) <- fmToList t]
          (g',attrs',f) = mkFiltration g ct
          ct = runST (do ct <- mkSTCollapsingTable g attrs
                         minimize' ct t
                         unsafeFreeze ct)

mkFiltration :: Graph -> CollapsingTable -> (Graph, Table Attr, Table Vertex)
mkFiltration g ct = (g', attrs, f)
    where (f,attrs,g') =
              case foldl phi (0,[],[],[]) (assocs ct) of
              (size, xs, ys, zs) ->
                  ( array (bounds g) xs
                  , array (0, size - 1) ys
                  , array (0, size - 1) zs
                  )
             where phi (n,xs,ys,zs) (_, Left _)            = (n,xs,ys,zs)
                   phi (n,xs,ys,zs) (v, Right (_,vs,attr)) =
                       ( n+1
                       , [(x,n) | x <- IS.toList vs] ++ xs
                       , (n, attr) : ys
                       , (n, nubAndSort $ map (f!) (g!v)) : zs
                       )

minimize' :: Ord u => STCollapsingTable st -> Tagging u -> ST st ()
minimize' g tagging =
    do assocs <- getAssocs g
       let b :: FiniteMap Rank Block
           b = addListToFM_C IS.union emptyFM
               [ (rank, IS.single x) | (x, Right (_,_,(_,rank))) <- assocs ]
       p' <- flip mapM (fmToList b) $ \(rank,block) ->
               do ref <- newSTRef [block]
                  return (rank,(ref,block))
       let p = listToFM p'

       case lookupFM p (Rank 0) of
           Just (ref,b0) -> writeSTRef ref (eltsFM fm)
               where fm = addListToFM_C IS.union emptyFM
                          [ (lookupFM tagging x, IS.single x)
                            | x <- IS.toList b0 ]
           Nothing -> return ()

       case lookupFM b RankNegInf of
           Just block -> do x <- collapseBlock g block
                            refine g (tail p') x
           Nothing -> return ()

       -- fmToList の結果がソートされてることを前提としている
       let loop [] = return ()
           loop ((rank,(ref,bi)) : ps) =
               do blocks <- readSTRef ref
                  blocks <- stabilize g rank bi blocks
                  flip mapM_ blocks $
                           \block -> do x <- collapseBlock g block
                                        refine g ps x
                  loop ps
       loop (fmToList (delFromFM p RankNegInf))


stabilize :: STCollapsingTable st -> Rank -> Block -> Partition -> ST st Partition
stabilize g rank b blocks =
    do let b'  = IS.toAscList b
           min = head b'
           max = last b'
       tmp <- flip mapM b' $ \x ->
                   do parents <- getParents g x
                      return (x, lookupWithDefaultFM parents IS.empty rank)
       let table :: Array Vertex (IS.IntSet)
           table = array (min, max) tmp
           ys = stabilize' (IS.size b) table blocks
       return ys

stabilize' :: Int -> Array Vertex IS.IntSet -> Partition -> Partition
stabilize' bsize table blocks = seq bsize $ seq table $ loop blocks blocks
    where loop :: Partition -> Partition -> Partition
          loop ps [] = ps
          loop ps (q:qs)
              | splitterSize == 0 ||
                splitterSize == bsize
                  = loop ps qs
              | otherwise =
                  case foldl phi ([],qs) ps of
                  (ps',qs') -> loop ps' qs'
              where splitter = IS.unions (map (table!) (IS.toList q))
                    splitterSize = IS.size splitter
                    phi (ps,qs) p = 
                        case splitIntSet splitter p of
                        Just (a,b) -> (a:b:ps, a:b:qs)
                        Nothing    -> (p:ps, qs)

{--------------------------------------------------------------------
  Utility functions
--------------------------------------------------------------------}

{-# INLINE splitIntSet #-}
splitIntSet :: IS.IntSet -> IS.IntSet -> Maybe (IS.IntSet, IS.IntSet)
splitIntSet splitter x
    | xsize < 2      = Nothing
    | isize == 0     = Nothing
    | isize == xsize = Nothing
    | otherwise      = Just (i, x `IS.difference` i)
    where xsize = IS.size x
          i     = x `IS.intersection` splitter
          isize = IS.size i

nubAndSort :: [Int] -> [Int]
nubAndSort = IS.toAscList . IS.fromList

-----------------------------------------------------------------------------
