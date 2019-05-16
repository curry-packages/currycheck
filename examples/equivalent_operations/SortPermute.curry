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
sorted (x:xs@(y:_)) = x<=y && sorted xs

psort :: Ord a => [a] -> [a]
psort xs | sorted ys = ys where ys = permute xs

------------------------------------------------------------------

idSorted :: Ord a => [a] -> [a]
idSorted [] = []
idSorted [x] = [x]
idSorted (x:xs@(y:_)) | x<=y = x : idSorted xs

isort :: Ord a => [a] -> [a]
isort xs = idSorted (permute xs)

------------------------------------------------------------------

-- Equivalence falsified by 1174th test:
equiv = psort <=> (isort :: [Int] -> [Int])

-- Equivalence falsified by 46th test:
equiv'TERMINATE = psort <=> (isort :: [Int] -> [Int])
