import Data.Graph
import Data.Array.IArray
import Data.Array.ST
import Data.FiniteMap
import Data.Set
import Data.List hiding (union)
import Data.STRef
import Control.Monad
import Control.Monad.ST

-----------------------------------------------------------------------------

type Tagging u = FiniteMap Vertex u
type TaggedGraph u = (Graph, Tagging u)

-----------------------------------------------------------------------------

type Rank = Maybe Int
-- Nothing means -∞.
-- Assuming that (Ord a => Ord (Maybe a)) and Nothing < Just _.

rankTable :: Graph -> Table Rank
rankTable g = fmap snd table
    where scc = stronglyConnComp [(x,x,ys) | (x,ys) <- assocs g]
          table = array (bounds g) (concatMap f scc)
          f (AcyclicSCC x) = [(x, (wf, rank))]
              where wf   = and [x | ch <- g!x, let (x,_) = table!ch]
                    rank = h x [x]
          f (CyclicSCC xs) = [(x, (wf, rank x)) | x<-xs]
              where wf     = False
                    rank x = h x xs
          h x xs
              | null (g!x)    = Just 0
              | isEmptySet ms = Nothing
              | otherwise =
                  foldl1 max [r' | ch <- setToList ms
                              , let (wf,r) = table ! ch
                                    r'     = if wf then fmap (+1) r else r]
              where ms = mkSet (concatMap (g!) xs) `minusSet` (mkSet xs)

rankTableTest1 = a==b
    where a = rankTable (array (0,2) [(0,[1,2]), (1,[1]), (2,[])])
          b = array (0,2) [(0,Just 1),(1,Nothing),(2,Just 0)]

rankTableTest2 = a==b
    where a = rankTable (array (0,4) [(0,[1,2]), (1,[0]), (2,[3,4]), (3,[2]), (4,[]) ])
          b = array (0,4) [(0,Just 1),(1,Just 1),(2,Just 1),(3,Just 1),(4,Just 0)]

-----------------------------------------------------------------------------

type G st = STArray st Vertex (Either Vertex (Set Vertex))

mkGFromGraph :: Graph -> ST st (G st)
mkGFromGraph g =
    newListArray (bounds g) [Right (mkSet e) | e <- elems g]

apply :: G st -> Vertex -> ST st Vertex
apply g x = do (x',_) <- apply' g x
               return x'            

apply' :: G st -> Vertex -> ST st (Vertex, Set Vertex)
apply' g x =
    do y' <- readArray g x
       case y' of
          Right children -> return (x,children)
          Left y ->
              do (z,children) <- apply' g y
                 unless (y==z) (writeArray g x (Left z))
                 return (z,children)

collapse :: G st -> Vertex -> Vertex -> ST st Vertex
collapse g a' b' =
    do (a,as) <- apply' g a'
       (b,bs) <- apply' g b'
       if a==b
          then return a
          else do writeArray g a' (Left b')
                  writeArray g b' (Right (as `union` bs))
                  return b'

collapseList :: G st -> [Vertex] -> ST st ()
collapseList g [] = return ()
collapseList g (x:xs) =
    do foldM (collapse g) x xs
       return ()

-----------------------------------------------------------------------------

type Partition = [Vertex]
type P st = FiniteMap Rank (STRef st [Partition])

refine :: G st -> P st -> Rank -> Vertex -> ST st ()
refine g p r v = mapM_ phi (fmToList p)
    where -- phi :: (Rank, STRef st [Partition]) -> ST st ()
          phi (k,ref)
              | k <= r    = return ()
              | otherwise = do ps <- readSTRef ref
                               ps' <- foldM psi [] ps
                               writeSTRef ref ps'
              where -- psi :: [Partition] -> Partition -> ST a [Partition]
                    psi ps p =
                        do (pa,pb) <- partitionM f p
                           return ([x | x <- [pa,pb], not (null x)] ++ ps)
                    -- f :: forall a. Vertex -> ST a Bool
                    f x = do (_,children) <- apply' g x
                             return (v `elementOf` children)

partitionM :: (Monad m) => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM f = foldM g ([],[])
    where g (a,b) x = do t <- f x
                         if t
                            then return (x:a,b)
                            else return (a,x:b)

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
               do collapseList g xs
                  refine g p Nothing x
       let loop (i,ref) =
               do when (i==Just 0) (modifySTRef ref (divideRank0 tagging))
                  di <- readSTRef ref
                  let f xs = do collapseList g xs
                                ns <- liftM nub (mapM (apply g) xs)
                                mapM_ (refine g p i) ns
                  mapM_ f di
       mapM_ loop (fmToList (delFromFM p Nothing))
       return g
    where rankT :: Table Rank
          rankT = rankTable graph
          maxRank :: Rank
          maxRank = foldl max Nothing (elems rankT)
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