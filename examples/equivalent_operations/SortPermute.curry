import Test.Prop

-- Definition of permute from library `Combinatorial` (part of PAKCS
-- distribution up to version 2.0.2 and contained in Curry package
-- `combinatorial` version 1.0.0).
--
-- Note that this definition is "spine strict", i.e., it does not return
-- any partial value for partial lists, e.g.,
-- head (permute (1:failed))  ---> no value!
permute        :: [a] -> [a]
permute []     = []
permute (x:xs) = ndinsert (permute xs)
    where ndinsert [] = [x]
          ndinsert (y:ys) = (x:y:ys) ? (y:ndinsert ys)

------------------------------------------------------------------

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted [_] = True
sorted (x:y:zs) = x<=y && sorted (y:zs)

psort :: Ord a => [a] -> [a]
psort xs | sorted ys = ys where ys = permute xs

------------------------------------------------------------------

idSorted :: Ord a => [a] -> [a]
idSorted [] = []
idSorted [x] = [x]
idSorted (x:y:zs) | x<=y = x : idSorted (y:zs)

isort :: Ord a => [a] -> [a]
isort xs = idSorted (permute xs)

------------------------------------------------------------------

-- Equivalence falsified by 1174th test:
equiv = psort <=> (isort :: [Int] -> [Int])

-- Equivalence falsified by 46th test:
equiv'TERMINATE = psort <=> (isort :: [Int] -> [Int])
