import Debug.QuickCheck
import Hyperset

prop_cardinalityNonNegative (x :: Set Int) = cardinality x >= 0
prop_cardinality1 (x :: Set Int) = cardinality x == length (toList x)

{-
prop_propersubsetIsSubset (x, y :: Set Int) =
    x `properSubsetOf` y ==> x `subsetOf` y
-}

prop_toList (x :: Set Int) = fromList (toList x) == x

prop_unionSize (x, y :: Set Int) =
    cardinality (x `union` y) <= cardinality x + cardinality y
prop_unionInclusion1 (x, y :: Set Int) = x `subsetOf` (x `union` y)
prop_unionInclusion2 (x,y :: Set Int)  = y `subsetOf` (x `union` y)

-- 時間がかかり過ぎないようにサイズを予め制限しておく
prop_powersetSize (x :: Set Int) =
    c <= 10 ==> 2^c == cardinality (powerset x)
    where c = cardinality x

prop_powerset (x :: Set Int) =
   (cardinality x) <= 10 ==>
        (Right x) `member` px && (Right emptySet) `member` px
    where px = powerset x