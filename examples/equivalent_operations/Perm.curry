import Test.Prop

-- Definition of permute from library Combinatorial
-- Note that this definition is "spine strict", i.e., it does not return
-- any partial value for partial lists, e.g.,
-- head (permute (1:failed))  ---> no value!
permute        :: [a] -> [a]
permute []     = []
permute (x:xs) = ndinsert (permute xs)
    where ndinsert [] = [x]
          ndinsert (y:ys) = (x:y:ys) ? (y:ndinsert ys)

-- An alternative, less strict definition of permutations, e.g.,
-- head (perm (1:failed))  --->  1
perm :: [a] -> [a]
perm []     = []
perm (x:xs) = ndinsert x (perm xs)
  where ndinsert x ys     = x : ys
        ndinsert x (y:ys) = y : ndinsert x ys

------------------------------------------------------------------

-- Equivalence falsified by 13th test:
permEquiv = perm <=> permute

-- Equivalence falsified by 3rd test:
permEquiv'TERMINATE = perm <=> permute

-- Ground equivalence not falsified:
permEquiv'GROUND xs = perm xs <~> permute xs
