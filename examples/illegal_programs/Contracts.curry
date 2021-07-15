---------------------------------------------------------------------------
-- Here are some examples for problems to be detected by CurryCheck
---------------------------------------------------------------------------

-- Examples for unintended uses of contracts:

-- Here there is no implementation of the operation `some`:
some'pre _ = True

some'post _ _ = True

some'spec x = x

-- The specification has a different type than the implementation:
k'spec x = x
k x _ = x

inc :: Int -> Int
inc n = n + 1

-- Illegal contract types:
inc'pre x = x

inc'post x y = x+y

---------------------------------------------------------------------------
