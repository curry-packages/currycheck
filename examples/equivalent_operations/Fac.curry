--- Example stating the equivalence of an iterative implementation
--- of the factorial function and its recursive specification.
---
--- To test it:
---
---     > curry-check Fac

-- Recursive definition of factorial.
-- Requires precondition to avoid infinite loops.
fac'spec :: Int -> Int
fac'spec n = if n==0 then 1 else n * fac'spec (n-1)

fac'spec'pre :: Int -> Bool
fac'spec'pre n = n >= 0

-- An iterative implementation of the factorial function.
-- Note that this implementation delivers 1 for negative numbers.
fac :: Int -> Int
fac n = faci 1 1
 where
  faci m p = if m>n then p else faci (m+1) (m*p)
  