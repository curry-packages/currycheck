--- Example to show the non-equivalence of two versions of the
--- `take` operation, taken from
---
--- Foner, K. and Zhang, H. and Lampropoulos, L.: {Keep Your Laziness in Check
--- ICFP 2018,
--- DOI: 10.1145/3236797

import Test.Prop

-- take operation from the Prelude:
take1 :: Int -> [a] -> [a]
take1 n xs | n <= 0    = []
           | otherwise = takep n xs
   where takep _ []     = []
         takep m (y:ys) = y : take1 (m-1) ys

-- take operation with different pattern matching:
take2 :: Int -> [a] -> [a]
take2 n [] = []
take2 n (x:xs) | n > 0     = x : take2 (n-1) xs
               | otherwise = []

-- The equality of both take operations on ground values always succeeds:
take_groundequiv x xs = take1 x xs <~> take2 x xs

-- Actually, take1 and take2 are not equivalent, as can be seen
-- by evaluating `take... failed [])` or `take... 0 failed`.
-- Thus, we check the equivalence with CurryCheck:

-- In PAKCS, the counter example is reported by the 11th test:
take_equiv = take1 <=> take2
