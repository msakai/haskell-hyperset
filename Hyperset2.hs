module Hyperset2 where

import Data.Graph
import Data.Array.IArray
import Data.Array.ST
import Data.FiniteMap
import qualified Data.Set as FS
import Data.List
import Data.STRef
import Control.Monad
import Control.Monad.ST
import Debug.Trace

-----------------------------------------------------------------------------

-- XXX:
instance (Ord k, Show k, Show e) => Show (FiniteMap k e) where
    showsPrec d fm = showsPrec d (fmToList fm)

powerList :: [a] -> [[a]]
powerList = foldr phi [[]]
    where phi a xs = map (a:) xs ++ xs

showSet :: (Show u, Ord u) => Set u -> String
showSet s | isWellfounded s = f s
          | otherwise = "non-wellfounded set"
    where f s = "{" ++ concat (intersperse "," (map g (toList s))) ++ "}"
          g (Left u)   = show u
          g (Right s') = f s'

-----------------------------------------------------------------------------

data Ord u => Set u = Set !(System u) !Vertex deriving Show

instance Ord u => Eq (Set u) where
    s1@(Set sys1 v1) == s2@(Set sys2 v2) =
        sysAttrTable sys1 ! v1 == sysAttrTable sys1 ! v2 &&
        cardinality s1 == cardinality s2 &&
        isBisimilar s1 s2

isBisimilar :: (Ord u) => Set u -> Set u -> Bool
isBisimilar s1@(Set sys1 v1) s2@(Set sys2 v2) = m!v1 == m!(v2+offset)
    where g1 = sysGraph sys1
          g2 = sysGraph sys2
          (lb1,ub1) = bounds g1
          (lb2,ub2) = bounds g2
          offset = ub1 + 1 - lb2
          mu = ub2 + offset + 1
          t' = sysTagging sys1 `plusFM` listToFM [(k+offset,e) | (k,e) <- fmToList (sysTagging sys2)]
          g' = array (lb1,mu) ((mu,[v1,v2+offset]) : assocs g1 ++ [(k+offset, map (offset+) e) | (k,e) <- assocs g2])
          (_,m) = minimize (g',t')

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
{-
solve (array (0,0) [(0,atom)])
=> array (0,0) [(0,Set (System (array (0,0) [(0,[0])]) []) 0)]

solve (array (0,1) [(0, fromList [Left (Right 1)]), (1, fromList [Left (Right 0)])])
=> array (0,1) [(0,Set (System (array (0,0) [(0,[0])]) []) 0),(1,Set (System (array (0,0) [(0,[0])]) []) 0)]
-}

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
powerset s@(Set sys v) = trace (seq g' $ show (g',t)) $ constructSet (g',t) v'
    where g = sysGraph sys
          t = sysTagging sys
          (lb,ub) = bounds g
          v' = ub + length p + 1
          p  = zip [(ub+1)..] (powerList (g!v))
          g' = array (lb, v') ((v', map fst p) : p ++ assocs g)

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

normalize :: Ord u => TaggedGraph u -> (System u, Table Vertex)
normalize (g,t) = (mkSystem g' t', m)
    where ((g',t'),m) = minimize (g,t)

-----------------------------------------------------------------------------

type Attr =
    ( Bool -- wellfounededness
    , Rank -- Rank
    )

type Rank = Maybe Int
-- Nothing means -∞.
-- Assuming that (Ord a => Ord (Maybe a)) and (∀x. Nothing < Just x).

rankTable :: Graph -> Table Rank
rankTable g = fmap snd (attrTable g)

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
              | null (g!x)       = Just 0
              | FS.isEmptySet ms = Nothing
              | otherwise =
                  foldl1 max [r' | ch <- FS.setToList ms
                              , let (wf,r) = table ! ch
                                    r'     = if wf then fmap (+1) r else r]
              where ms = FS.mkSet (concatMap (g!) xs) `FS.minusSet` FS.mkSet xs

rankTableTest1 = a==b
    where a = rankTable (array (0,2) [(0,[1,2]), (1,[1]), (2,[])])
          b = array (0,2) [(0,Just 1),(1,Nothing),(2,Just 0)]

rankTableTest2 = a==b
    where a = rankTable (array (0,4) [(0,[1,2]), (1,[0]), (2,[3,4]), (3,[2]), (4,[]) ])
          b = array (0,4) [(0,Just 1),(1,Just 1),(2,Just 1),(3,Just 1),(4,Just 0)]

-----------------------------------------------------------------------------

type G st = STArray st Vertex (Either Vertex (FS.Set Vertex))

mkGFromGraph :: Graph -> ST st (G st)
mkGFromGraph g =
    newListArray (bounds g) [Right (FS.mkSet e) | e <- elems (transposeG g)]

apply :: G st -> Vertex -> ST st Vertex
apply g x = do (x',_) <- apply' g x
               return x'            

apply' :: G st -> Vertex -> ST st (Vertex, FS.Set Vertex)
apply' g x =
    do y' <- readArray g x
       case y' of
          Right parents -> return (x,parents)
          Left y ->
              do (z, parents) <- apply' g y
                 unless (y==z) (writeArray g x (Left z))
                 return (z, parents)

collapse :: G st -> Vertex -> Vertex -> ST st Vertex
collapse g a' b' =
    do (a,as) <- apply' g a'
       (b,bs) <- apply' g b'
       if a==b
          then return a
          else do writeArray g a' (Left b')
                  writeArray g b' (Right (as `FS.union` bs))
                  return b'

collapseList :: G st -> [Vertex] -> ST st Vertex
collapseList g []     = return undefined
collapseList g (x:xs) = foldM (collapse g) x xs

-----------------------------------------------------------------------------

type Partition = [Vertex]
type P st = FiniteMap Rank (STRef st [Partition])

refine :: G st -> P st -> Rank -> Vertex -> ST st ()
refine g p r v =
    do (_,vs) <- apply' g v
       mapM_ (phi vs) (fmToList p)
    where -- phi :: FS.Set Vertex -> (Rank, STRef st [Partition]) -> ST st ()
          phi vs (k,ref)
              | k <= r    = return ()
              | otherwise = modifySTRef ref (concatMap f)
              where f p = [x | x <- [pa,pb], not (null x)]
                        where (pa,pb) = partition (`FS.elementOf` vs) p

-----------------------------------------------------------------------------

minimize :: (Ord u) => TaggedGraph u -> (TaggedGraph u, Table Vertex)
minimize tg@(g,t) = ((g',t'), m)
    where g' = array (0, sizeFM fm - 1)
                 [(i, sort $ nub $ [m!ch | ch <- g!x]) | (i,x:_) <- c]
          t' = listToFM [(m!v,u) | (v,u) <- fmToList t]
          m = array (bounds g) [(x,i) | (i,xs) <- c, x <- xs]
          c :: [(Int,[Vertex])]
          c = zip [0..] (eltsFM fm)
          fm :: FiniteMap Vertex [Vertex]
          fm = addListToFM_C (\old new -> new++old) emptyFM
                 [(v',[v]) | (v,v') <- m1]
          m1 :: [(Vertex,Vertex)]
          m1 = runST (do gg <- minimize' tg
                         mapM (\v -> do v' <- apply gg v; return (v,v'))
                              (indices g))

minimize' :: (Ord u) => TaggedGraph u -> ST st (G st)
minimize' (graph, tagging) =
    do g <- mkGFromGraph graph
       p_ <- mapM (\(r,vs) -> do ref <- newSTRef [vs]; return (r,ref))
                  (fmToList b)
       let p = listToFM p_
       case lookupFM b Nothing of
           Nothing -> return ()
           Just xs@(x:_) ->
               do x <- collapseList g xs
                  refine g p Nothing x
       case lookupFM p (Just 0) of
           Just ref -> modifySTRef ref (divideRank0 tagging)
           Nothing  -> return ()
       let loop (i,ref) =
               do di <- readSTRef ref
                  let f xs@(x:_) = do x <- collapseList g xs
                                      refine g p i x
                  mapM_ f di
       mapM_ loop (fmToList (delFromFM p Nothing))
       return g
    where rankT :: Table Rank
          rankT = rankTable graph
          b :: FiniteMap Rank [Vertex]
          b = addListToFM_C (\old new -> new++old) emptyFM
                            [(r,[x]) | (x,r) <- assocs rankT]

divideRank0 :: (Ord u) => Tagging u -> [Partition] -> [Partition]
divideRank0 tagging ps = eltsFM fm
    where fm = addListToFM_C (\old new -> new++old) emptyFM
                             [(lookupFM tagging x, [x]) | x <- concat ps]

-----------------------------------------------------------------------------

{-
http://citeseer.ist.psu.edu/cache/papers/cs/29860/http:zSzzSzwww.dimi.uniud.itzSz~piazzazSzPAPERSzSzcav01.pdf/dovier00fast.pdf

R. Paige and R. E. Tarjan. Three partition refinement algorithms. SIAM Journal on Computing, 16(6):973-989, 1987.
を探さなくては
-}