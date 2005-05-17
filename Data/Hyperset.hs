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

module Data.Hyperset
    (
    -- * The @Set@ type
      Set
    , Elem (..)

    -- * Operators
    , (\\)

    -- * Inspection
    , isWellfounded
    , size
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

import Prelude hiding (null)
import Data.Graph (Graph,Vertex,Table,scc)
import Data.Tree (Tree,flatten)
import Data.Array.IArray hiding (elems)
import Data.Array.ST
import Data.STRef
import Data.Maybe (fromJust)
import qualified Data.List as List (mapAccumL, null)
import qualified Data.Map as Map
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import Control.Monad (unless, foldM)
import Control.Monad.ST (ST)

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

instance Ord u => Eq (Set u) where
    s1 == s2 | isEmpty s1 && isEmpty s2 = True
    s1@(Set sys1 v1) == s2@(Set sys2 v2) =
        getAttr s1 == getAttr s2 &&
        size s1 == size s2 &&
        in1 v1 == in2 v2
        where (_,in1,in2) = mergeSystem sys1 sys2

-- for debugging
instance (Ord u, Show u) => Show (Set u) where
    showsPrec d s = showsPrec d (g, v, IM.toList t)
       where (g,v,t) = picture s

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- |Is this a well-founded set?
isWellfounded :: Ord u => Set u -> Bool
isWellfounded s = case getAttr s of
		  (wf,_) -> wf

getAttr :: Ord u => Set u -> Attr
getAttr (Set sys v) = sysAttrTable sys ! v

-- |The number of elements in the set.
size :: Ord u => Set u -> Int
size (Set sys v) = length (sysGraph sys ! v)

-- |Is this the empty set?
isEmpty :: Ord u => Set u -> Bool
isEmpty x = size x == 0

-- |Is this a singleton set?.
isSingleton :: Ord u => Set u -> Bool
isSingleton x = size x == 1

-- XXX: 汚いなぁ
-- |Is the element in the set?
member :: Ord u => Elem u -> Set u -> Bool
member (Urelem x) (Set sys v) =
    any (\y -> IM.lookup y t == Just x) (g!v)
    where t = sysTagging sys
          g = sysGraph sys
member (SetElem s1) (Set sys v) | isEmpty s1 =
    any (\y -> List.null (g!y) && IM.lookup y t == Nothing) (g!v)    
    where t = sysTagging sys
          g = sysGraph sys
member (SetElem (Set sys1 v1)) (Set sys2 v2) =
    in1 v1 `elem` (g ! in2 v2)
    where (sys,in1,in2) = mergeSystem sys1 sys2
          g = sysGraph sys

_subset :: Ord u => Set u -> Set u -> Bool
s `_subset` _ | isEmpty s = True
(Set sys1 v1) `_subset` (Set sys2 v2) = xs `IS.isSubsetOf` ys
    where g1 = sysGraph sys1
          g2 = sysGraph sys2
          (_,in1,in2) = mergeSystem sys1 sys2
          xs = IS.fromList (map in1 (g1 ! v1))
          ys = IS.fromList (map in2 (g2 ! v2))

-- |Is this a subset?
-- @(s1 \`subset\` s2)@ tells whether s1 is a subset of s2.
subset :: Ord u => Set u -> Set u -> Bool
as `subset` bs = size as <= size bs && as `_subset` bs

-- |Is this superset?
-- @(s1 \`superset\` s2)@ tells whether s1 is a superset of s2.
superset :: Ord u => Set u -> Set u -> Bool
as `superset` bs = bs `subset` as

-- |Is this a proper subset?
-- @(s1 \`properSubset\` s2)@ tells whether s1 is a proper subset of s2.
properSubset :: Ord u => Set u -> Set u -> Bool
as `properSubset` bs = size as < size bs && as `_subset` bs

-- |Is this a proper subset?
-- @(s1 \`properSuperset\` s2)@ tells whether s1 is a proper superset of s2.
properSuperset :: Ord u => Set u -> Set u -> Bool
as `properSuperset` bs = bs `properSubset` as

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- |Quine atom: x={x}.
quineAtom :: Ord u => Set u
quineAtom = toSet sys 0
    where (sys,_) = mkSystem (listArray (0,0) [[0]])
                             IM.empty
                             (listArray (0,0) [(False,RankNegInf)])

-- |The empty set.
empty :: Ord u => Set u
empty = fromList []

-- |Create a singleton set.
singleton :: Ord u => Elem u -> Set u
singleton u = fromList [u]

-- |The powerset of the set.
powerset :: Ord u => Set u -> Set u
powerset (Set sys v) = toSet sys' (f ! v')
    where (v',sys',f) = mkSystem3 $
                        do instSys sys
                           xs <- mapM addSet (powerList (sysGraph sys ! v))
                           addSet xs

-- Mark Jones' powerSet
-- http://www.haskell.org/pipermail/haskell-cafe/2003-June/004484.html
powerList :: [a] -> [[a]]
powerList = foldr phi [[]]
    where phi x xs = xs /\/ map (x:) xs
          []     /\/ ys = ys
          (x:xs) /\/ ys = x : (ys /\/ xs)

-- |The union of two sets.
union :: Ord u => Set u -> Set u -> Set u
union (Set sys1 v1) (Set sys2 v2) = toSet sys' (f ! v')
    where (v',sys',f) = mkSystem3 $
                        do instSys sys1
                           off <- instSys sys2
                           addSet (map (off+) (g2!v2) ++ g1!v1)
          g1 = sysGraph sys1
          g2 = sysGraph sys2

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
equivClass r (Set sys v) = toSet sys' (f ! v')
    where r' a b = r (toElem sys a) (toElem sys b)
          (v',sys',f) = mkSystem3 $
                        do instSys sys
                           let xs = classifyList r' (sysGraph sys ! v)
                           ys <- mapM addSet xs
                           addSet ys

classifyList :: (a -> a -> Bool) -> [a] -> [[a]]
classifyList f = foldl phi []
    where phi (s:ss) x | f (head s) x = (x:s) : ss
                       | otherwise    = s : phi ss x
          phi [] x = [[x]]

-- |Filter all elements that satisfy the predicate.
separate :: Ord u => (Elem u -> Bool) -> (Set u -> Set u)
separate f (Set sys v) = toSet sys' (m ! v')
    where (v',sys',m) = mkSystem3 $
                        do instSys sys
                           addSet [ch | ch <- sysGraph sys ! v
                                  , f (toElem sys ch)]

-- partition :: Ord u => (Elem u -> Bool) -> Set u -> (Set u, Set u)

toElem :: Ord u => System u -> Vertex -> Elem u
toElem sys v = case IM.lookup v (sysTagging sys) of
               Just e  -> Urelem e
               Nothing -> SetElem (Set sys v)

toSet :: Ord u => System u -> Vertex -> Set u
toSet sys v = Set sys v

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
    where (sys,m) = mkSystemFromTaggedGraph tg
	  tg = mkTaggedGraphFromEquations equations

-- XXX: 汚いなぁ
mkTaggedGraphFromEquations :: Ord u => SystemOfEquations u -> TaggedGraph u
mkTaggedGraphFromEquations equations = (array (lb,ub') l, t)
    where (lb,ub) = bounds equations
          (ub',l,t) = foldl phi (ub,[],IM.empty) (assocs equations)
          phi (ub,l,t) (lhs, (Set sys v)) = (ub', l', t')
              where g = sysGraph sys
                    m :: Array Var Vertex
                    m = array (bounds g) m'
                    ((ub',l',t'), m') = List.mapAccumL psi (ub,l,t) (assocs g)
                        where psi (ub,l,t) (x,children)
                               | v==x =
                                   ( (ub, (lhs, map (m!) children) : l, t)
                                   , (x, lhs)
                                   )
                               | otherwise =
                                   case IM.lookup x (sysTagging sys) of
                                   Just (Right v) ->
                                       ((ub,l,t), (x,v))
                                   Just (Left u) ->
                                       ( ( ub+1
                                         , (ub+1,[]) : l
                                         , IM.insert (ub+1) u t
					 )
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
-- For a childless node v of G, we interpret @IntMap.lookup v t == Just u@
-- as t(v)=u, @IntMap.lookup v t == Nothing@ as t(v)=φ.
type Tagging u = IM.IntMap u

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
    where (sys,m) = mkSystemFromTaggedGraph (g,t)
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
fromList xs = toSet sys (f ! v)
    where (v,sys,f) = mkSystem3 $
                      do ys <- flip mapM xs $ \x->
                               case x of
                                   Urelem u -> addUrelem u
                                   SetElem (Set sys v) ->
                                       do off <- instSys sys
                                          return (off+v)
                         addSet ys

{--------------------------------------------------------------------
  Implementation
--------------------------------------------------------------------}

type TaggedGraph u = (Graph, Tagging u)

data System u =
    System
    { sysGraph        :: !Graph
    , sysTagging      :: !(Tagging u)
    , sysAttrTable    :: !(Table Attr)
    }

mergeSystem :: Ord u => System u -> System u ->
               (System u, Vertex -> Vertex, Vertex -> Vertex)
mergeSystem sys1 sys2 = (sys, in1, in2)
    where (off,sys,f) = mkSystem3 $ instSys sys1 >> instSys sys2
          in1 i = f!i
          in2 i = f!(i+off)

type GenState u =
    ( Int
    , [(Int,[Int])]
    , Tagging u
    , IM.IntMap Attr
    )
newtype Gen u a = Gen{ runGen :: GenState u -> (GenState u, a) }

{-# INLINE returnG #-}
returnG :: Ord u => a -> Gen u a
returnG a = Gen (\s -> (s,a))

{-# INLINE bindG #-}
bindG :: Ord u => Gen u a -> (a -> Gen u b) -> Gen u b
bindG ma f = Gen (\s -> case runGen ma s of
                        (s',a) -> runGen (f a) s')

instance (Ord u) => Monad (Gen u) where
    return = returnG
    (>>=)  = bindG

instSys :: Ord u => System u -> Gen u Vertex
instSys sys = Gen $ \(n,g,t,a) ->
    ( ( n + (rangeSize (bounds (sysGraph sys)))
      , [(v+n, map (n+) xs) | (v,xs) <- assocs (sysGraph sys)] ++ g
      , IM.fromAscList [(k+n,v) | (k,v) <- IM.toAscList (sysTagging sys)]
	`IM.union` t
      , IM.fromAscList [(k+n,v) | (k,v) <- assocs (sysAttrTable sys)]
	`IM.union` a
      )
    , n
    )

addSet :: Ord u => [Vertex] -> Gen u Vertex
addSet children = Gen $ \(n,g,t,a) ->
    ( ( n+1
      , (n, children) : g
      , t
      , IM.insert n (attrOfSetFromElemAttrs
		     [fromJust (IM.lookup ch a) | ch <- children]) a
      )
    , n
    )

addUrelem :: Ord u => u -> Gen u Vertex
addUrelem u = Gen $ \(n,g,t,a) ->
    ( ( n+1
      , (n,[]) : g
      , IM.insert n u t
      , IM.insert n attrUrelem a
      )
    , n
    )

mkSystem3 :: Ord u => Gen u a -> (a, System u, Table Vertex)
mkSystem3 gen =
    case runGen gen (0,[],IM.empty,IM.empty) of
    ((n,g,t,a),val) ->
        let attrs = array (0,n-1) (IM.toList a) in
            case mkSystem (array (0,n-1) g) t attrs of
            (sys, f) -> (val, sys, f)

-----------------------------------------------------------------------------

data Rank
    = RankNegInf -- -∞
    | Rank {-# UNPACK #-} !Int
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

-----------------------------------------------------------------------------

type Attr =
    ( Bool -- wellfounededness
    , Rank -- Rank
    )

attrUrelem :: Attr
attrUrelem = (True, Rank 0)

attrTable :: Graph -> Table Attr
attrTable g = table
    where table = array (bounds g)
                  [(x,(wf,rank)) | (xs,wf,rank) <- sccInfo, x <- IS.toList xs]
          gS = fmap IS.fromList g
          sccInfo :: [(IS.IntSet, Bool, Rank)]
          sccInfo = map f (scc g)
          f :: Tree Vertex -> (IS.IntSet, Bool, Rank)
          f sccT = (sccS, wf, rank)
              where sccL = flatten sccT
                    sccS = IS.fromList sccL
                    wf = case sccL of
                         [x] | x `IS.member` (gS!x) -> False
                             | otherwise  ->
                                 and [wf | ch <- g!x, let (wf,_) = table!ch]
                         _ -> False
                    rank = case sccL of
                           [x] | List.null (g!x) -> Rank 0
                           _   | IS.null children -> RankNegInf
                               | otherwise ->
                                   maximum
                                   [ if wf then succRank r else r
                                   | ch <- IS.toList children
                                   , let (wf,r) = table ! ch
                                   ]
                    children = IS.unions (map (gS!) sccL) `IS.difference` sccS

-- 要素のAttrから集合のAttrを計算
attrOfSetFromElemAttrs :: [Attr] -> Attr
attrOfSetFromElemAttrs [] = (True, Rank 0)
attrOfSetFromElemAttrs xs =
    ( foldr (&&) True (map fst xs)
    , foldl phi RankNegInf xs
    )
    where phi rank1 a = case f a of rank2 -> rank1 `max` rank2
              where f (True,rank)  = succRank rank
                    f (False,rank) = rank

-----------------------------------------------------------------------------

type PreimageMap = Map.Map Rank IS.IntSet

mkPreimageTable :: Graph -> Table Attr -> Array Vertex PreimageMap
mkPreimageTable g t = runSTArray (f g t)
    where f :: Graph -> Table Attr -> ST st (STArray st Vertex PreimageMap)
          f g t =
              do table <- newListArray (bounds g) (repeat Map.empty)
                 flip mapM_ (assocs g) $ \(v,children) ->
                   do let (_,rank) = t!v
                          v' = IS.singleton v
                      flip mapM_ children $ \ch ->
                          do fm <- readArray table ch
                             let fm' = Map.insertWith IS.union rank v' fm
                             writeArray table ch fm'
                 return table

-----------------------------------------------------------------------------

type Block = IS.IntSet
type Partition = [Block]

type CellInfo =
    ( Map.Map Rank IS.IntSet
    , IS.IntSet
    , Attr
    )

type CollapsingTable      = Array Vertex (Either Vertex CellInfo)
type STCollapsingTable st = STArray st Vertex (Either Vertex CellInfo)

mkSTCollapsingTable :: Graph -> Table Attr -> ST st (STCollapsingTable st)
mkSTCollapsingTable g table =
    do let t :: Array Vertex PreimageMap
           t = mkPreimageTable g table
       newListArray (bounds g) [ Right (t!v, IS.singleton v, table!v)
                               | v <- indices g ]

getNodeInfo :: STCollapsingTable st -> Vertex -> ST st (Vertex, Map.Map Rank IS.IntSet, IS.IntSet, Attr)
getNodeInfo g x =
    do y <- readArray g x
       case y of
          Right (parents,vs,attr) -> return (x,parents,vs,attr)
          Left y1 -> getNodeInfo g y1

getParents :: STCollapsingTable st -> Vertex -> ST st (Map.Map Rank IS.IntSet)
getParents g v =
    do (_,parents,_,_) <- getNodeInfo g v
       return parents

collapse :: STCollapsingTable st -> Vertex -> Vertex -> ST st Vertex
collapse g a' b' =
    do (a,pas,as,attr) <- getNodeInfo g a'
       (b,pbs,bs,_)    <- getNodeInfo g b'
       if a==b
          then return a
          else do writeArray g a $ Right ( Map.unionWith IS.union pas pbs
                                         , as `IS.union` bs
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
       unless (Map.null parents) $
           flip mapM_ p $ \(rank, (ref,_)) ->
                case Map.lookup rank parents of
                Just xs -> modifySTRef ref (split xs)
                Nothing -> return ()

split :: IS.IntSet -> Partition -> Partition
split splitter xs = foldr phi [] xs
    where phi x ys = case splitIntSet splitter x of
                     Just (a,b) -> a : b : ys
                     Nothing    -> x : ys

-----------------------------------------------------------------------------

mkSystemFromTaggedGraph :: Ord u => TaggedGraph u -> (System u, Table Vertex)
mkSystemFromTaggedGraph (g,t) = mkSystem g t attrs
    where attrs = attrTable g

mkSystem :: Ord u =>
	    Graph -> Tagging u -> Table Attr -> (System u, Table Vertex)
mkSystem g t attrs =
    ( System
      { sysGraph     = g'
      , sysTagging   = IM.filterWithKey (\v _ -> List.null (g' ! v)) t'
      , sysAttrTable = attrs'
      }
    , f
    )
    where t' = IM.fromAscList [(f!k,v) | (k,v) <- IM.toAscList t]
          (g',attrs',f) = mkFiltration g ct
          ct = runSTArray (do ct <- mkSTCollapsingTable g attrs
                              minimize ct t
                              return ct)

mkFiltration :: Graph -> CollapsingTable -> (Graph, Table Attr, Table Vertex)
mkFiltration g ct = ret
    where ret@(_,_,f) =
              case foldl phi (0,[],[],[]) (assocs ct) of
              (size, xs, ys, zs) ->
                  ( array (0, size - 1) xs
                  , array (0, size - 1) ys
                  , array (bounds g) zs
                  )
             where phi ret (_, Left _) = ret
                   phi (n,xs,ys,zs) (v, Right (_,vs,attr)) =
                       ( n+1
                       , (n, nubAndSort $ map (f!) (g!v)) : xs
                       , (n, attr) : ys
                       , [(x,n) | x <- IS.toList vs] ++ zs
                       )

minimize :: Ord u => STCollapsingTable st -> Tagging u -> ST st ()
minimize g tagging =
    do assocs <- getAssocs g
       let b :: Map.Map Rank Block
           b = Map.fromListWith IS.union
               [ (rank, IS.singleton x) | (x, Right (_,_,(_,rank))) <- assocs ]
       p' <- flip mapM (Map.toAscList b) $ \(rank,block) ->
               do ref <- newSTRef [block]
                  return (rank,(ref,block))
       let p = Map.fromAscList p'

       case Map.lookup (Rank 0) p of
           Just (ref,b0) -> writeSTRef ref (Map.elems fm)
               where fm = Map.fromListWith IS.union
                          [ (IM.lookup x tagging, IS.singleton x)
                            | x <- IS.toList b0 ]
		     --lookupMaybe :: Ord k => k -> Map.Map k a -> Maybe a
		     --lookupMaybe = Map.lookup -- XXX
           Nothing -> return ()

       case Map.lookup RankNegInf b of
           Just block -> do x <- collapseBlock g block
                            refine g (tail p') x
           Nothing -> return ()

       let loop [] = return ()
           loop ((rank,(ref,bi)) : ps) =
               do blocks <- readSTRef ref
                  blocks <- stabilize g rank bi blocks
                  flip mapM_ blocks $
                           \block -> do x <- collapseBlock g block
                                        refine g ps x
                  loop ps
       loop (Map.toAscList (Map.delete RankNegInf p))


stabilize :: STCollapsingTable st -> Rank -> Block -> Partition -> ST st Partition
stabilize g rank b blocks =
    do let b'  = IS.toAscList b
           min = head b'
           max = last b'
       tmp <- flip mapM b' $ \x ->
                   do parents <- getParents g x
                      return (x, Map.findWithDefault IS.empty rank parents)
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
