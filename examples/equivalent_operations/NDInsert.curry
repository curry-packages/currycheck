--- Example to show the non-equivalence of two versions of a
--- non-deterministic insert operation.

import Test.Prop

-- Non-deterministic defined by overlapping rules:
ndinsert1 :: a -> [a] -> [a]
ndinsert1 x ys     = x : ys
ndinsert1 x (y:ys) = y : ndinsert1 x ys

-- Non-deterministic defined by non-overlapping rules:
ndinsert2 :: a -> [a] -> [a]
ndinsert2 x []     = [x]
ndinsert2 x (y:ys) = x : y : ys  ?  y : ndinsert2 x ys

-- The equality of both ndinsert operations on ground values always succeeds:
ndinsert_groundequiv x xs = ndinsert1 x xs <~> ndinsert2 x xs

-- Actually, ndinsert1 and ndinsert2 are not equivalent, as can be seen
-- by evaluating `head (ndinsert 1 failed)`.
-- Thus, we check the equivalence with CurryCheck:

-- In PAKCS, the counter example is reported by the 7th test:
ndinsert_equiv = ndinsert1 <=> ndinsert2

