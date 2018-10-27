--- Example stating the correctness of selection sort
---
--- To test it:
---
---     > curry-check SelectionSort

-- Permutations:
perm :: [a] -> [a]
perm []     = []
perm (x:xs) = insert x (perm xs)
  where insert x ys     = x : ys
        insert x (y:ys) = y : insert x ys

-- Is a list sorted?
sorted :: [Int] -> Bool
sorted []       = True
sorted [_]      = True
sorted (x:y:ys) = x<=y && sorted (y:ys)

-- Sort specification via sorted permutations:
sort'spec :: [Int] -> [Int]
sort'spec xs | sorted ys = ys where ys = perm xs

-- Implementation of sort as straight selection sort:
sort :: [Int] -> [Int]
sort []     = []
sort (x:xs) = case minRest x [] xs of (m,r) -> m : sort r
-- Note that the following definition would not be correct:
--
-- sort (x:xs) = m : sort r  where (m,r) = minRest x [] xs
--
-- This is due to the fact that it is less strict than the
-- specification, e.g., `null (sort (failed:failed))` would yield `False`
-- whereas the specification fails on this expression.

-- Implementations of minRest with a single list traversal:
minRest :: Int -> [Int] -> [Int] -> (Int,[Int])
minRest m rs []     = (m,rs)
minRest m rs (y:ys) = if m<=y then minRest m (y:rs) ys
                              else minRest y (m:rs) ys
