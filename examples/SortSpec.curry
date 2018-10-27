-- A specification of sorting a list and an implementation based
-- on the quicksort algorithm.
-- CurryCheck generates and checks properties which states
-- that the implementation is satisfies the specification
-- and the post-condition.

perm []     = []
perm (x:xs) = insert x (perm xs)
 where
   insert x ys     = x : ys
   insert x (y:ys) = y : insert x ys

sorted []       = True
sorted [_]      = True
sorted (x:y:ys) | x<=y && sorted (y:ys) = True

-- Postcondition: input and output lists should have the same length
sort'post xs ys = length xs == length ys

-- Specification of sort:
-- A list is a sorted result of an input if it is a permutation and sorted.
sort'spec :: [Int] -> [Int]
sort'spec xs | sorted ys = ys
 where ys = perm xs

-- An implementation of sort with quicksort:
sort :: [Int] -> [Int]
sort []     = []
sort (x:xs) = sort (filter (<x) xs) ++ [x] ++ sort (filter (>=x) xs)
