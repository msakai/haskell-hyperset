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

main :: IO ()
main =
    do print test0
       print test1
       print test2
       
{-
powerset $ powerset $ powerset atom
Set (System (array (0,14) [(0,[0]),(1,[0,13]),(2,[13]),(3,[0,1,2,13]),(4,[0,1,2]),(5,[0,1]),(6,[0,2,13]),(7,[0,2]),(8,[1,2,13]),(9,[1,2]),(10,[1]),(11,[2,13]),(12,[2]),(13,[]),(14,[0,1,2,3,4,5,6,7,8,9,10,11,12,13])]) []) 14

 0 = {0}        = Ω
 1 = {0,13}     = {Ω,φ}
 2 = {13}       = {φ}
 3 = {0,1,2,13} = {Ω, {Ω,φ}, {φ}, φ}
 4 = {0,1,2}    = {Ω, {Ω,φ}, {φ}}
 5 = {0,1}      = {Ω, {Ω,φ}}
 6 = {0,2,13}   = {Ω, {φ}, φ}
 7 = {0,2}      = {Ω, {φ}}
 8 = {1,2,13}   = {{Ω,φ}, {φ}, φ}
 9 = {1,2}      = {{Ω,φ}, {φ}}
10 = {1}        = {{Ω,φ}}
11 = {2,13}     = {{φ}, φ}
12 = {2}        = {{φ}}
13 = {}         = φ

 1 = {0,13}     = {Ω,φ}
 5 = {0,1}      = {Ω, {Ω,φ}}
 7 = {0,2}      = {Ω, {φ}}
 9 = {1,2}      = {{Ω,φ}, {φ}}
11 = {2,13}     = {{φ}, φ}

{{Ω,φ}, φ} が抜けている

 4 = {0,1,2}    = {Ω, {Ω,φ}, {φ}}
 6 = {0,2,13}   = {Ω, {φ}, φ}
 8 = {1,2,13}   = {{Ω,φ}, {φ}, φ}

{Ω,{Ω,φ}, φ} が抜けている


array (0,21) [(0,[0]),(1,[0,3]),(2,[3]),(3,[]),(4,[0,1,2,3]),(5,[0,1,2,3]),(6,[0,1,2]),(7,[0,1,3]),(8,[0,1]),(9,[0,2,3]),(10,[0,2]),(11,[0,3]),(12,[0]),(13,[1,2,3]),(14,[1,2]),(15,[1,3]),(16,[1]),(17,[2,3]),(18,[2]),(19,[3]),(20,[]),(21,[5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20])]

array (0,21) [(0,(False,Nothing)),(1,(False,Just 1)),(2,(True,Just 1)),(3,(True,Just 0)),(4,(False,Just 2)),(5,(False,Just 2)),(6,(False,Just 2)),(7,(False,Just 1)),(8,(False,Just 1)),(9,(False,Just 2)),(10,(False,Just 2)),(11,(False,Just 1)),(12,(False,Nothing)),(13,(False,Just 2)),(14,(False,Just 2)),(15,(False,Just 1)),(16,(False,Just 1)),(17,(True,Just 2)),(18,(True,Just 2)),(19,(True,Just 1)),(20,(True,Just 0)),(21,(False,Just 3))]

0 = Ω
1 = {0,3} = {Ω,φ}
2 = {3} = {φ}
3 = φ
7 = {0,1,3} = {Ω,{Ω,φ},φ}
11 = {0,3} = {Ω,φ}

0,12    => 0
1,7,11  => 1
2,15,19 => 2
4,5     => 3
6       => 4
8       => 5
9       => 6
10      => 7
13      => 8
14      => 9
16      => 10
17      => 11
18      => 12
3,20    => 13
21      => 14

array (0,21) [(0,0),(1,1),(2,2),(3,13),(4,3),(5,3),(6,4),(7,1),(8,5),(9,6),(10,7),(11,1),(12,0),(13,8),(14,9),(15,2),(16,10),(17,11),(18,12),(19,2),(20,13),(21,14)]


-}