-- Testing the equivalence of non-terminating operations:

import Test.Prop

-- Two different infinite lists:
primes :: [Int]
primes = sieve [2..]
 where sieve (x:xs) = x : sieve (filter (\y -> y `mod` x > 0) xs)

dummy_primes :: [Int]
dummy_primes = 2 : [3,5..]

-- This property will be falsified by the 38th test:
primes_equiv'PRODUCTIVE = primes <=> dummy_primes
