import Debug.QuickCheck
import Hyperset

prop_eqReflexive (x :: Set Int)  = x==x
prop_eqSymmetry (x :: Set Int) y = (x==y) == (y==x)

prop_cardinalityNonNegative (x :: Set Int) = cardinality x >= 0
prop_cardinality1 (x :: Set Int) = cardinality x == length (toList x)

{-
prop_propersubsetIsSubset (x :: Set Int) y =
    x `properSubsetOf` y ==> x `subsetOf` y
-}

prop_toList (x :: Set Int) = fromList (toList x) == x

prop_unionSize (x :: Set Int) y =
    cardinality (x `union` y) <= cardinality x + cardinality y &&
    cardinality x <= cardinality (x `union` y) &&
    cardinality y <= cardinality (x `union` y)
    
prop_unionInclusion (x :: Set Int) y = x `subsetOf` z && y `subsetOf` z
    where z = x `union` y

prop_intersectionSize (x :: Set Int) y  = 
    cardinality (x `intersection` y) <= cardinality x &&
    cardinality (x `intersection` y) <= cardinality y
prop_intersectionInclusion (x, y :: Set Int) = z `subsetOf` x && z `subsetOf` y
    where z = x `intersection` y


-- 時間がかかり過ぎないようにサイズを予め制限しておく

prop_powersetSize (x :: Set Int) =
    c <= 10 ==> 2^c == cardinality (powerset x)
    where c = cardinality x

prop_powerset1 (x :: Set Int) =
    (cardinality x) <= 8 ==> all f (toList (powerset x))
    where f (Left _)  = False
	  f (Right z) = z `subsetOf` x

prop_powerset2 (x :: Set Int) =
   (cardinality x) <= 10 ==>
        (Right x) `member` px && (Right emptySet) `member` px
    where px = powerset x
