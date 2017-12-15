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

-- Permutation sort in a different formulation (which is actually not
-- equivalent to psort):
isort :: Ord a => [a] -> [a]
isort xs = idSorted (perm xs)
 where idSorted []              = []
       idSorted [x]             = [x]
       idSorted (x:y:ys) | x<=y = x : idSorted (y:ys)

-- The equality of psort and isort on ground values (which always succeeds
-- when tested with CurryCheck):
--psort_and_isort x = psort x <~> isort x

-- Actually, psort and isort are not equivalent, as can be seen by evaluating
-- `head (isort [2,3,1])`.
-- Thus, we check the equivalence with CurryCheck (and provide type annotations
-- to avoid error message w.r.t. polymorphic types with unspecifed type class
-- contexts):

-- In PAKCS, the counter example is reported by the 274th test:
psort_equiv_isort = psort <=> (isort :: [Int] -> [Int])

-- In PAKCS, the counter example is reported by the 21th test:
psort_equiv_isort'TERMINATE = psort <=> (isort :: [Int] -> [Int])
