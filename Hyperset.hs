module Hyperset
    ( Set

    , atom
    , emptySet
    , singleton
    , Var
    , solve

    , toList
    , fromList

    , powerset
    , union
    , intersection
    , difference
    , equivClass
    , separate
    , mapSet

    , member
    , subsetOf
    , supersetOf
    , properSubsetOf
    , properSupersetOf
    , isWellfounded
    , cardinality
    , isEmptySet
    , isSingleton
    ) where

import Data.Graph
import Data.Array.IArray
import Data.Array.ST
import Data.FiniteMap
import qualified Data.Set as FS
import Data.List hiding (union)
import Data.STRef
import Control.Monad
import Control.Monad.ST.Strict
import Debug.Trace

-----------------------------------------------------------------------------

data Ord u => Set u = Set !(System u) !Vertex deriving Show

instance Ord u => Eq (Set u) where
    s1@(Set sys1 v1) == s2@(Set sys2 v2) =
        sysAttrTable sys1 ! v1 == sysAttrTable sys1 ! v2 &&
        cardinality s1 == cardinality s2 &&
        in1!v1 == in2!v2
        where (sys,in1,in2) = sumSystem sys1 sys2

isWellfounded :: Ord u => Set u -> Bool
isWellfounded (Set sys v) =
    case (sysAttrTable sys ! v) of
    (wf,_) -> wf

cardinality :: Ord u => Set u -> Int
cardinality (Set sys v) = length (sysGraph sys ! v)

isEmptySet :: Ord u => Set u -> Bool
isEmptySet x = cardinality x == 0

isSingleton :: Ord u => Set u -> Bool
isSingleton x = cardinality x == 1

-- 汚いなぁ
member :: Ord u => (Either u (Set u)) -> Set u -> Bool
member (Left x) (Set sys v) =
    any (\y -> lookupFM t y == Just x) (g!v)
    where t = sysTagging sys
          g = sysGraph sys
member (Right s1) (Set sys v) | isEmptySet s1 =
    any (\y -> null (g!y) && lookupFM t y == Nothing) (g!v)
    where t = sysTagging sys
          g = sysGraph sys
member (Right (Set sys1 v1)) (Set sys2 v2) =
    (in1 ! v1) `elem` (g ! (in2 ! v2))
    where (sys,in1,in2) = sumSystem sys1 sys2
          g = sysGraph sys

_subsetOf, subsetOf, supersetOf, properSubsetOf, properSupersetOf
    :: Ord u => Set u -> Set u -> Bool

s1 `_subsetOf` s2 | isEmptySet s1 = True
(Set sys1 v1) `_subsetOf` (Set sys2 v2) =
    FS.mkSet (map (in1!) (g1 ! v1)) == FS.mkSet (map (in2!) (g1 ! v2))
    where g1 = sysGraph sys1
          g2 = sysGraph sys2
          (sys,in1,in2) = sumSystem sys1 sys2

as `subsetOf`   bs = cardinality as <= cardinality bs && as `_subsetOf` bs
as `supersetOf` bs = bs `subsetOf` as
as `properSubsetOf`   bs = cardinality as < cardinality bs && as `_subsetOf` bs
as `properSupersetOf` bs = bs `properSubsetOf` as

wrap :: Ord u => System u -> Vertex -> Either u (Set u)
wrap sys v = case lookupFM (sysTagging sys) v of
             Just e  -> Left e
             Nothing -> Right (Set sys v)

constructSet :: Ord u => TaggedGraph u -> Vertex -> Set u
constructSet tg v = case wrap sys (m!v) of
                    Right set -> set
                    --Left _ -> error "shouldn't happen"
    where (sys,m) = normalize tg

atom :: Ord u => Set u
atom = constructSet (array (0,0) [(0,[0])], emptyFM) 0

-- elems って名前の方がよい?
toList :: Ord u => Set u -> [Either u (Set u)]
toList (Set sys v) = map (wrap sys) (sysGraph sys ! v)

fromList :: Ord u => [Either u (Set u)] -> Set u
fromList xs = constructSet (array (0,n) ((n,children):l), t) n
    where ((n,l,t), children) = mapAccumL phi (0,[],emptyFM) xs
          phi (n,l,t) (Left u) =
              ((n+1, (n,[]):l, addToFM t n u), n)
          phi (n,l,t) (Right (Set sys v)) =
              ((ub+off+1, l'++l, addListToFM t t'), v+off)
              where (lb,ub) = bounds (sysGraph sys)
                    off = n - lb
                    l'  = [(v+off, [ch+off | ch <- children])
                           | (v,children) <- assocs (sysGraph sys)]
                    t'  = [(v+off,u) | (v,u) <- fmToList (sysTagging sys)]

emptySet :: Ord u => Set u
emptySet = fromList []

singleton :: Ord u => Either u (Set u) -> Set u
singleton u = fromList [u]

type Var = Int

solve :: Ord u => Array Var (Set (Either u Var)) -> Array Var (Set u)
solve equations = array (bounds equations)
                  [(i,x)
                   | i <- indices equations
                   , let Right x = wrap sys (m!i)]
    where (sys,m)  = normalize $ mkTaggedGraphFromEquations equations

-- XXX: 汚いなぁ
mkTaggedGraphFromEquations
    :: Ord u => Array Var (Set (Either u Var)) -> TaggedGraph u
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

-- XXX: 汚いなぁ
powerset :: (Show u, Ord u) => Set u -> Set u
powerset s@(Set sys v) = constructSet (g',t) v'
    where g = sysGraph sys
          t = sysTagging sys
          (lb,ub) = bounds g
          v' = ub + length p + 1
          p  = zip [(ub+1)..] (powerList (g!v))
          g' = array (lb, v') ((v', map fst p) : p ++ assocs g)

powerList :: [a] -> [[a]]
powerList = foldr phi [[]]
    where phi a xs = map (a:) xs ++ xs

-- XXX: 汚いなぁ
union :: Ord u => Set u -> Set u -> Set u
union (Set sys1 v1) (Set sys2 v2) = constructSet (g,t) v
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

-- unionManySets :: Ord u => Set u -> Set u

-- 効率が悪い
intersection :: Ord u => Set u -> Set u -> Set u
a `intersection` b = separate (\x -> x `member` b) a

-- 効率が悪い
difference :: Ord u => Set u -> Set u -> Set u
a `difference` b = separate (\x -> not (x `member` b)) a

equivClass :: Ord u => (Either u (Set u) -> Either u (Set u) -> Bool) ->
                       (Set u -> Set u)
equivClass f (Set sys v) = constructSet (g', sysTagging sys) v'
    where f' a b = f (wrap sys a) (wrap sys b)
          g = sysGraph sys
          l = zip [ub+1..] (classify f' (g ! v))
          (lb,ub) = bounds (sysGraph sys)
          v' = ub + length l + 1
          g' = array (lb, v') ((v', map fst l) : l ++ assocs g)

classify :: (a -> a -> Bool) -> [a] -> [[a]]
classify f = foldl phi []
    where phi (s:ss) x | f (head s) x = (x:s) : ss
                       | otherwise    = s : phi ss x
          phi [] x = [[x]]

-- filter という名前の方がよい?
separate :: Ord u => (Either u (Set u) -> Bool) -> (Set u -> Set u)
separate f s@(Set sys v) =
    constructSet (g',t) v'
    where g = sysGraph sys
          t = sysTagging sys
          (lb,ub) = bounds g
          g'  = array (lb,ub+1) (foo : assocs g)
              where foo = (v', [child | child <- g!v, f (wrap sys child)])
          v'  = ub+1

-- partition :: Ord u => (Either u (Set u) -> Bool) -> Set u -> (Set u, Set u)

mapSet :: (Ord u, Ord u') =>
          (Either u (Set u) -> Either u' (Set u')) -> (Set u -> Set u')
mapSet f = fromList . map f . toList

-----------------------------------------------------------------------------

type Tagging u = FiniteMap Vertex u
type TaggedGraph u = (Graph, Tagging u)

data System u =
    System
    { sysGraph        :: !Graph
    , sysTagging      :: !(Tagging u)
    , sysAttrTable    :: (Table Attr)
    }

-- XXX
instance (Ord u, Show u) => (Show (System u)) where
    showsPrec d System{ sysGraph = g, sysTagging = t}
        | d == 11   = ('(':) . f . (')':)
        | otherwise = f
        where f = ("System "++) . (showsPrec 11 g) . (' ':)
                  . (showsPrec 11 (fmToList t))

mkSystem :: Ord u => Graph -> Tagging u -> System u
mkSystem g t =
    System{ sysGraph      = g
          , sysTagging    = t'
          , sysAttrTable  = attrTable g
          }
    where t' = filterFM (\v _ -> null (g!v)) t

sumSystem :: Ord u => System u -> System u ->
             (System u, Table Vertex, Table Vertex)
sumSystem sys1 sys2 = (sys, in1, in2)
    where g1 = sysGraph sys1
          g2 = sysGraph sys2
          (offset, lb, ub) = (ub1 + 1 - lb2, lb1, ub2+offset)
              where (lb1,ub1) = bounds g1
                    (lb2,ub2) = bounds g2
          in1 = array (bounds g1) [(i,m!i) | i <- indices g1]
          in2 = array (bounds g2) [(i,m!(i+offset)) | i <- indices g2]
          (sys,m) = normalize (g,t)
              where g = array (lb,ub) (assocs g1 ++ [(k+offset, map (offset+) e) | (k,e) <- assocs g2])
                    t = t1 `plusFM` t2
                        where t1 = sysTagging sys1
                              t2 = listToFM [(k+offset,e) | (k,e) <- fmToList (sysTagging sys2)]

normalize :: Ord u => TaggedGraph u -> (System u, Table Vertex)
normalize (g,t) = (mkSystem g' t', m)
    where ((g',t'),m) = minimize (g,t)

-----------------------------------------------------------------------------

type Attr =
    ( Bool -- wellfounededness
    , Rank -- Rank
    )

data Rank
    = Rank !Int
    | RankNegInf -- -∞
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
    where scc = stronglyConnComp [(x,x,ys) | (x,ys) <- assocs g]
          table = array (bounds g) (concatMap f scc)
          f (AcyclicSCC x) = [(x, (wf, rank))]
              where wf   = and [x | ch <- g!x, let (x,_) = table!ch]
                    rank = h x [x]
          f (CyclicSCC xs) = [(x, (wf, rank x)) | x<-xs]
              where wf     = False
                    rank x = h x xs
          h x xs
              | null (g!x)       = Rank 0
              | FS.isEmptySet ms = RankNegInf
              | otherwise =
                  foldl1 max [r' | ch <- FS.setToList ms
                              , let (wf,r) = table ! ch
                                    r'     = if wf then succRank r else r]
              where ms = FS.mkSet (concatMap (g!) xs) `FS.minusSet` FS.mkSet xs

{-
rankTable :: Graph -> Table Rank
rankTable g = fmap snd (attrTable g)

rankTableTest1 = a==b
    where a = rankTable (array (0,2) [(0,[1,2]), (1,[1]), (2,[])])
          b = array (0,2) [(0,Rank 1),(1,RankNegInf),(2,Rank 0)]

rankTableTest2 = a==b
    where a = rankTable (array (0,4) [(0,[1,2]), (1,[0]), (2,[3,4]), (3,[2]), (4,[]) ])
          b = array (0,4) [(0,Rank 1),(1,Rank 1),(2,Rank 1),(3,Rank 1),(4,Rank 0)]
-}

-----------------------------------------------------------------------------

type G st = STArray st Vertex (Either Vertex (FS.Set Vertex, FS.Set Vertex))

mkG :: Graph -> ST st (G st)
mkG g =
    newListArray (bounds g) [Right (FS.mkSet parents, FS.unitSet v)
                             | (v, parents) <- assocs (transposeG g)]

apply :: G st -> Vertex -> ST st Vertex
apply g x = do (x',_,_) <- apply' g x
               return x'

apply' :: G st -> Vertex -> ST st (Vertex, FS.Set Vertex, FS.Set Vertex)
apply' g x =
    do y' <- readArray g x
       case y' of
          Right (parents,vs) -> return (x,parents,vs)
          Left y ->
              do (z, parents, vs) <- apply' g y
                 unless (y==z) (writeArray g x (Left z)) -- 経路圧縮
                 return (z, parents, vs)

collapse :: G st -> Vertex -> Vertex -> ST st Vertex
collapse g a' b' =
    do (a,pas,as) <- apply' g a'
       (b,pbs,bs) <- apply' g b'
       if a==b
          then return a
          else do writeArray g a' (Left b')
                  writeArray g b' (Right (pas `FS.union` pbs, as `FS.union` bs))
                  return b'

collapseList :: G st -> [Vertex] -> ST st Vertex
collapseList g []     = return undefined
collapseList g (x:xs) = foldM (collapse g) x xs

-----------------------------------------------------------------------------

type Block = FS.Set Vertex
type P st = FiniteMap Rank (STRef st [Block])

refine :: G st -> [(Rank, STRef st [Block])] -> Rank -> Vertex -> ST st ()
refine g p rank v =
    do (_,parents,_) <- apply' g v
       mapM_ (phi parents) p
    where -- phi :: FS.Set Vertex -> (Rank, STRef st [Block]) -> ST st ()
          phi parents (i,ref)
              | i <= rank = return ()
              | otherwise = modifySTRef ref (foldr phi [])
              where phi p ps
                        | fsIsSingleton p = p : ps
                        | otherwise =
                            case fsSplit p parents of
                            Just (a,b) -> a : b : ps
                            Nothing    -> p : ps

-----------------------------------------------------------------------------

minimize :: (Ord u) => TaggedGraph u -> (TaggedGraph u, Table Vertex)
minimize tg@(g,t) = ((g',t'), m)
    where t' = listToFM [(m!v,u) | (v,u) <- fmToList t]
          (m,g') = case foldl phi (0,[],[]) hoge of
                        (size, xs, ys) ->
                            ( array (bounds g) xs
                            , array (0, size - 1) ys
                            )
             where phi (n,xs,ys) (v, Left _)       = (n, xs, ys)
                   phi (n,xs,ys) (v, Right (_,vs)) =
                       ( n+1
                       , [(x,n) | x <- FS.setToList vs] ++ xs
                       , (n, sort $ nub $ map (m!) (g!v)) : ys
                       )
                   hoge = runST (do gg <- minimize' tg
                                    assocs <- getAssocs gg
                                    return assocs)

-- あんましFiniteMap使う必然性はないんだよなぁ
minimize' :: (Ord u) => TaggedGraph u -> ST st (G st)
minimize' (graph, tagging) =
    do g <- mkG graph
       let b :: FiniteMap Rank Block
           b = addListToFM_C (\old new -> new `FS.union` old) emptyFM
                             [(rank, FS.unitSet x)
                              | (x,(_,rank)) <- assocs (attrTable graph)]
       p' <- mapM (\(rank,vs) -> do ref <- newSTRef [vs]; return (rank,ref))
                  (fmToList b)
       let -- p :: P st
           p = listToFM p'
       case lookupFM b RankNegInf of
           Just xs -> do x <- collapseList g (FS.setToList xs) -- XXX
                         refine g p' RankNegInf x
           Nothing -> return ()
       case lookupFM p (Rank 0) of
           Just ref -> modifySTRef ref (divideRank0 tagging)
           Nothing  -> return ()
       let loop (rank, ref) =
               do di <- readSTRef ref
                  let (Just bi) = lookupFM b rank
                  di <- stabilize g bi di
                  let f xs = do x <- collapseList g (FS.setToList xs) -- XXX
                                refine g p' rank x
                  mapM_ f di
       -- fmToList の結果がソートされてることを前提としている
       mapM_ loop (fmToList (delFromFM p RankNegInf))
       return g

divideRank0 :: (Ord u) => Tagging u -> [Block] -> [Block]
divideRank0 tagging ps = eltsFM fm
    where fm = addListToFM_C (\old new -> new `FS.union` old) emptyFM
                             [(lookupFM tagging x, FS.unitSet x)
                              | x <- concatMap FS.setToList ps]

stabilize :: G st -> Block -> [Block] -> ST st [Block]
stabilize g b xs =
    do let b' = FS.setToList b
       tmp <- mapM (\x ->
                    do (_,parents,_) <- apply' g x
                       return (x, parents `FS.intersect` b)) b'
       let table :: Array Vertex (FS.Set Vertex)
           table = array (head b', last b') tmp
                   -- setToList の結果はソートされているので、
                   -- headとlastで最小元と最大元が得られる           
           ys  = f table xs
       return ys
    where f :: Array Vertex (FS.Set Vertex) -> [Block] -> [Block]
          f table xs = loop [] xs xs
              where loop :: [Block] -> [Block] -> [Block] -> [Block]
                    loop ss [] qs     = ss
                    loop ss ps []     = ss ++ ps
                    loop ss ps (q:qs) = case foldl phi (ss,[],qs) ps of
                                        (ss',ps',qs') -> loop ss' ps' qs'
                        where splitter = FS.unionManySets
                                           (map (table!) (FS.setToList q))
                              phi (ss,ps,qs) p
                                  | fsIsSingleton p = (p:ss, ps, qs)
                                  | otherwise =
                                      case fsSplit p splitter of
                                      Just (a,b) -> (ss, a:b:ps, a:b:qs)
                                      Nothing    -> (ss, p:ps, qs)

-----------------------------------------------------------------------------
-- utility

-- XXX:
instance (Ord k, Show k, Show e) => Show (FiniteMap k e) where
    showsPrec d fm = showsPrec d (fmToList fm)

-- XXX:
showSet :: (Show u, Ord u) => Set u -> String
showSet s | isWellfounded s = f s
          | otherwise = "non-wellfounded set"
    where f s = "{" ++ concat (intersperse "," (map g (toList s))) ++ "}"
          g (Left u)   = show u
          g (Right s') = f s'

{-# INLINE fsIsSingleton #-}
fsIsSingleton :: (Ord a) => FS.Set a -> Bool
fsIsSingleton x = FS.cardinality x == 1

{-# INLINE fsSplit #-}
fsSplit :: (Ord a) => FS.Set a -> FS.Set a -> Maybe (FS.Set a, FS.Set a)
fsSplit x splitter = seq x $ seq splitter $
      if isize == 0
      then Nothing
      else if isize == FS.cardinality x
           then Nothing
           else Just (i, x `FS.minusSet` i)
    where i = x `FS.intersect` splitter
          isize = FS.cardinality i

-----------------------------------------------------------------------------

