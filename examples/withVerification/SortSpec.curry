-- A specification of sorting a list and an implementation based
-- on insertion sort.
-- CurryCheck generates and checks properties which states
-- that the implementation is satisfies the specification
-- and the post-condition.
--
-- To demonstrate the use of statically proven properties,
-- we include a theorem that is used to simplify the postcondition
-- of sort.

import Test.Prop

perm []     = []
perm (x:xs) = ndinsert x (perm xs)
 where
   ndinsert x ys     = x : ys
   ndinsert x (y:ys) = y : ndinsert x ys

sorted []       = True
sorted [_]      = True
sorted (x:y:ys) | x<=y && sorted (y:ys) = True

-- Postcondition: input and output lists should have the same length
sort'post xs ys = length xs == length ys && sorted ys

-- Specification of sort:
-- A list is a sorted result of an input if it is a permutation and sorted.
sort'spec :: [Int] -> [Int]
sort'spec xs | sorted ys = ys
 where ys = perm xs

-- An implementation of sort with quicksort:
sort :: [Int] -> [Int]
sort []     = []
sort (x:xs) = insert x (sort xs)

insert :: Int -> [Int] -> [Int]
insert x [] = [x]
insert x (y:ys) = if x<=y then x : y : ys
                          else y : insert x ys

-- A theorem about the length of sorting a list.
-- If this theorem is proved (i.e., if there is a file
-- `proof-sort-preserves-length.*`),
-- it is not checked but used to simplify the postcondition sort'post.
sortPreservesLength xs = length (sort xs) <~> length xs
