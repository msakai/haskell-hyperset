import Hyperset
import Data.Array
import Data.List
import qualified Data.IntMap as IntMap

showSet :: (Show u, Ord u) => Set u -> String
showSet s | isWellfounded s = f s
	  | otherwise = "non-wellfounded set"
    where f s = "{" ++ concat (intersperse "," (map g (toList s))) ++ "}"
	  g (Urelem u)   = show u
	  g (SetElem s') = f s'

test0 :: Set Int
--test0 = fromList [Right atom, Right emptySet]
test0 = fromList [Urelem 0, Urelem 1]

test1 :: Set Int
test1 = powerset test0

test2 :: Set Int
test2 = powerset test1

test3 :: Bool
test3 = size (powerset x) == 8
    where x :: Set Int
          SetElem x = decorate (array (0,4) [(0,[1,3,4]),(1,[0,1,2,4]),(2,[]),(3,[2,3,4]),(4,[])]) (IntMap.fromList [(4,-1)]) ! 0

testSolve :: Bool
testSolve = solutions!0 /= (solutions!1 :: Set Int)
    where solutions = solve eqns
          eqns = array (0,1)
                 [ (0, fromList [ SetElem (fromList [ Urelem $ Left 0 ])
                                , SetElem (fromList [ Urelem $ Left 0
						    , Urelem $ Left 1 ])
                                ])
                 , (1, fromList [ SetElem (fromList [ Urelem $ Left 0
						    , Urelem $ Left 1])
                                ] )
                 ]

-- equivClass (\(Left n) (Left m) -> n `mod` 3 == m `mod` 3) (fromList [Left 1, Left 2, Left 3, Left 4])
testEquivClass :: Bool
testEquivClass = (a :: Set Int) == b
    where a = equivClass (\(Urelem n) (Urelem m) -> n `mod` 3 == m `mod` 3) (fromList [Urelem 1, Urelem 2, Urelem 3, Urelem 4])
          b = fromList [ SetElem (fromList [Urelem 1, Urelem 4])
	               , SetElem (singleton (Urelem 2))
	               , SetElem (singleton (Urelem 3))
	               ]

main :: IO ()
main =
    do print test0
       print test1
       print test2
