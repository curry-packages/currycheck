-- Testing the equivalence of non-terminating operations:

import Nat
import Test.Prop

-- Two different infinite lists:
ints1 n = n : ints1 (n+1)

ints2 n = n : ints2 (n+2)

-- Falsified by 47th test:
ints1_equiv_ints2 = ints1 <=> ints2

