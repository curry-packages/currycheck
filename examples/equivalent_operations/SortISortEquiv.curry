import Test.Prop

-- Permutation sort:
psort :: Ord a => [a] -> [a]
psort xs | sorted ys = ys where ys = perm xs

perm []     = []
perm (x:xs) = ndinsert x (perm xs)
  where ndinsert x ys     = x : ys
        ndinsert x (y:ys) = y : ndinsert x ys

sorted []       = True
sorted [_]      = True
sorted (x:y:ys) = x<=y & sorted (y:ys)

-- Insertion sort: The list is sorted by repeated sorted insertion
-- of the elements into the already sorted part of the list.
insSort :: Ord a => [a] -> [a]
insSort []     = []
insSort (x:xs) = insert (insSort xs)
 where
  insert []     = [x]
  insert (y:ys) = if x<=y then x : y : ys
                          else y : insert ys

-- Test equivalence of psort and isort (and provide type annotations
-- to avoid error message w.r.t. polymorphic types with unspecifed type class
-- contexts):

psort_equiv_insSort'TERMINATE = psort <=> (insSort :: [Int] -> [Int])
