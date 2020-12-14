{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=defaultrules #-}

--- Examples for specifying deterministic operations via
--- the DET annotation in the type.
--- CurryCheck generates and check properties which states
--- that the original operations are indeed deterministic.

-- Computes the last element of a list.
last :: Data a => [a] ->DET a
last (_ ++ [x]) = x

last'pre :: Data a => [a] -> Bool
last'pre = not . null

-- Definition of bubble sort with default rule as a deterministic operaion.
sort :: [Int] ->DET [Int]
sort (xs++[x,y]++ys) |  x>y = sort (xs++[y,x]++ys)
sort'default xs = xs


