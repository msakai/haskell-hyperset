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

-- これを実用的な計算量で計算できるようにしたいなぁ。
hoge :: Set ()
hoge = powerset $ powerset $ powerset $ powerset atom

-- Trueになるべきだけど、現在はFalseになってしまう
testSolve :: Bool
testSolve = solutions!0 /= solutions!1
    where solutions = solve eqns
          eqns = array (0,1)
                 [ (0, fromList [ Right emptySet
                                , Right (fromList [Left $ Left 0])
                                , Right (fromList [Left $ Left 0, Left $ Left 1])
                                ])
                 , (1, fromList [ Right emptySet
                                , Right (fromList [Left $ Left 0, Left $ Left 1])
                                ] )
                 ]

main :: IO ()
main =
    do print test0
       print test1
       print test2