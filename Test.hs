import Hyperset
import Array
import List (intersperse)

showSet :: (Show u, Ord u) => Set u -> String
showSet s | isWellfounded s = f s
	  | otherwise = "non-wellfounded set"
    where f s = "{" ++ concat (intersperse "," (map g (toList s))) ++ "}"
	  g (Left u)   = show u
	  g (Right s') = f s'

test0 :: Set Int
--test0 = fromList [Right atom, Right emptySet]
test0 = fromList [Left 0, Left 1]

test1 :: Set Int
test1 = powerset test0

test2 :: Set Int
test2 = powerset test1

-- Trueになるべきだけど、現在はFalseになってしまう
testSolve :: Bool
testSolve = solutions!0 /= solutions!1
    where solutions = solve eqns
          eqns = array (0,1)
                 [ (0, fromList [ Right (fromList [Left $ Left 0])
                                , Right (fromList [Left $ Left 0, Left $ Left 1])
                                ])
                 , (1, fromList [ Right (fromList [Left $ Left 0, Left $ Left 1])
                                ] )
                 ]

-- equivClass (\(Left n) (Left m) -> n `mod` 3 == m `mod` 3) (fromList [Left 1, Left 2, Left 3, Left 4])
testEquivClass :: Bool
testEquivClass = a == b
    where a = equivClass (\(Left n) (Left m) -> n `mod` 3 == m `mod` 3) (fromList [Left 1, Left 2, Left 3, Left 4])
          b = fromList [ Right (fromList [Left 1, Left 4])
	               , Right (singleton (Left 2))
	               , Right (singleton (Left 3))
	               ]

main :: IO ()
main =
    do print test0
       print test1
       print test2
