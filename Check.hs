import Debug.QuickCheck
import Hyperset

prop_unionSize (x,y) =
    cardinality (x `union` y) <= cardinality x + cardinality y
    where hoge = x :: Set Int

prop_unionInclusion1 (x,y) = x `subsetOf` (x `union` y)
    where hoge = x :: Set Int

prop_unionInclusion2 (x,y) = y `subsetOf` (x `union` y)
    where hoge = x :: Set Int

main = quickCheck prop_unionInclusion1