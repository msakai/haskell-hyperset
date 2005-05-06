import Hyperset

-- これを実用的な計算量で計算できるようにしたいなぁ。
hoge :: Set ()
hoge = powerset $ powerset $ powerset $ powerset quineAtom

fuga :: Set Int
fuga = powerset (fromList l)
    where l = SetElem a : SetElem b : SetElem c : map Urelem [0..9]
          a = powerset (powerset (powerset quineAtom))
          b = powerset (powerset (powerset (powerset empty)))
          c = singleton (SetElem (singleton (SetElem (fromList [Urelem i | i <- [0..9]]))))

fuga2 :: Set Int
fuga2 = powerset (fromList l)
    where l = SetElem a : SetElem b : SetElem c : SetElem d : map Urelem [0..10]
          a = powerset (powerset (powerset quineAtom))
          b = powerset (powerset (powerset (powerset empty)))
          c = singleton (SetElem (singleton (SetElem (fromList [Urelem i | i <- [0..100]]))))
	  d = a `union` b


main :: IO ()
main = putStrLn $ show $ size $ fuga

