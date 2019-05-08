--- Example from:
--- 
--- Olaf Chitil:
--- StrictCheck: a Tool for Testing Whether a Function is Unnecessarily Strict
--- University of Kent, TR 2-11, 2011
--- https://kar.kent.ac.uk/30756/

import Test.Prop

--- Definition of unzip from the standard prelude.
unzip1 :: [(a,b)] -> ([a],[b])
unzip1 []         = ([],[])
unzip1 ((x,y):ps) = (x:xs,y:ys) where (xs,ys) = unzip1 ps

--- Definition from Chitil'11:
unzip2 :: [(a,b)] -> ([a],[b])
unzip2 xs = foldr (\ (a,b) (as,bs) -> (a:as,b:bs)) ([],[]) xs

-- Equivalence falsified by 27th test:
unzipEquiv = unzip1 <=> unzip2

-- Equivalence falsified by 6th test:
unzipEquiv'TERMINATE = unzip1 <=> unzip2

-- Ground equivalence is not falsified:
unzipEquiv'GROUND xs = unzip1 xs <~> unzip2 xs
