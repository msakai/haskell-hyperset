import Hyperset

-- これを実用的な計算量で計算できるようにしたいなぁ。
hoge :: Set ()
hoge = powerset $ powerset $ powerset $ powerset atom

fuga :: Set Int
fuga = powerset (fromList l)
    where l = Right a : Right b : map Left [0..9]
	  a = powerset (powerset (powerset atom))
	  b = powerset (powerset (powerset (powerset emptySet)))

main :: IO ()
main = putStrLn $ show $ cardinality $ fuga
