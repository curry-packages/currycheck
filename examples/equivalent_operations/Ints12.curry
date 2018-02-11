-- Testing the equivalence of non-terminating operations:

import Nat
import Test.Prop

-- Two different infinite lists:
ints1 :: Int -> [Int]
ints1 n = n : ints1 (n+1)

ints2 :: Int -> [Int]
ints2 n = n : ints2 (n+2)

-- This property will be falsified by the 47th test:
ints1_equiv_ints2 = ints1 <=> ints2
