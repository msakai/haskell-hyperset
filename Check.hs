-----------------------------------------------------------------------------

import Hyperset
import Data.Graph
import Data.Array
import Data.List (sort,nub)
import Data.FiniteMap
import Debug.QuickCheck
import Control.Monad (foldM)

-----------------------------------------------------------------------------

instance (Ord u, Arbitrary u) => Arbitrary (Set u) where
    arbitrary =
        do g <- genGraph
           t <- genTagging g
           let d = decorate g t
               f [] = arbitrary
               f (Left _ : xs)  = f xs
               f (Right x : xs) = return x
           f (elems d)
    coarbitrary set =
        variant v . coarbitrary (fmToList t) . coarbitrary (assocs g)
        where (g,v,t) = picture set

genGraph :: Gen Graph
genGraph = sized genGraph'
    where genGraph' n =
              do ub <- choose (0,n)
                 xs <- mapM (genChildren ub) [0..ub]
                 return (array (0,ub) xs)
          genChildren ub x =
              do y <- choose (0,ub*2)
                 children <- sequence (take y (repeat (choose (0,ub))))
                 return (x, sort $ nub $ children) -- FIXME

genTagging :: (Ord u, Arbitrary u) => Graph -> Gen (Tagging u)
genTagging g = 
    do l <- foldM f [] [i | (i,children) <- assocs g, null children]
       return (listToFM l)
    where f as x =
              do b <- arbitrary
                 if b
                    then return as
                    else do e <- arbitrary
                            return ((x,e) : as)

-----------------------------------------------------------------------------

prop_eqReflexive :: Set Int -> Bool
prop_eqReflexive x = x==x

prop_eqSymmetry :: Set Int -> Set Int -> Bool
prop_eqSymmetry x y = (x==y) == (y==x)

-----------------------------------------------------------------------------

prop_cardinalityNonNegative :: Set Int -> Bool
prop_cardinalityNonNegative x = cardinality x >= 0

prop_cardinality1 :: Set Int -> Bool
prop_cardinality1 x = cardinality x == length (toList x)

-----------------------------------------------------------------------------

prop_toList :: Set Int -> Bool
prop_toList x = fromList (toList x) == x

-----------------------------------------------------------------------------

prop_unionAssoc	:: Set Int -> Set Int -> Set Int -> Bool
prop_unionAssoc	x y z = (x `union` y) `union` z == x `union` (y `union` z)

prop_unionComm :: Set Int -> Set Int -> Bool
prop_unionComm x y = x `union` y == y `union` x

prop_unionAbsorb :: Set Int -> Set Int -> Bool
prop_unionAbsorb x y = (x `union` y) `union` y == (x `union` y)

prop_unionSize :: Set Int -> Set Int -> Bool
prop_unionSize x y =
    cardinality (x `union` y) <= cardinality x + cardinality y &&
    cardinality x <= cardinality (x `union` y) &&
    cardinality y <= cardinality (x `union` y)

prop_unionInclusion :: Set Int -> Set Int -> Bool
prop_unionInclusion x y = x `isSubsetOf` z && y `isSubsetOf` z
    where z = x `union` y

-----------------------------------------------------------------------------

prop_intersectionAssoc :: Set Int -> Set Int -> Set Int -> Bool
prop_intersectionAssoc x y z = (x `intersection` y) `intersection` z == x `intersection` (y `intersection` z)

prop_intersectionComm :: Set Int -> Set Int -> Bool
prop_intersectionComm s1 s2 = s1 `intersection` s2 == s2 `intersection` s1

prop_intersectionAbsorb :: Set Int -> Set Int -> Bool
prop_intersectionAbsorb x y = (x `intersection` y) `intersection` y == (x `intersection` y)

prop_intersectionSize :: Set Int -> Set Int -> Bool
prop_intersectionSize x y  = 
    cardinality (x `intersection` y) <= cardinality x &&
    cardinality (x `intersection` y) <= cardinality y

prop_intersectionInclusion :: Set Int -> Set Int -> Bool
prop_intersectionInclusion x y = z `isSubsetOf` x && z `isSubsetOf` y
    where z = x `intersection` y

-----------------------------------------------------------------------------
-- 時間がかかり過ぎないようにサイズを予め制限しておく

prop_powersetSize :: Set Int -> Property
prop_powersetSize x =
    c <= 8 ==> 2^c == cardinality (powerset x)
    where c = cardinality x

prop_powerset1 :: Set Int -> Property
prop_powerset1 x =
    (cardinality x) <= 8 ==> all f (toList (powerset x))
    where f (Left _)  = False
          f (Right z) = z `isSubsetOf` x

prop_powerset2 :: Set Int -> Property
prop_powerset2 x =
   (cardinality x) <= 8 ==>
        (Right x) `member` px && (Right empty) `member` px
    where px = powerset x

-----------------------------------------------------------------------------