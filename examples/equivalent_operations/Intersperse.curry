--- Example from:
--- 
--- Christiansen, J. and Seidel, D.: Minimally strict polymorphic functions
--- Proc. of the 13th International Symposium on Principle and Practice
--- of Declarative Programming (PPDP'11), pp. 53-64
--- DOI: 10.1145/2003476.2003487

import Test.Prop

--- Definition of `intersperse` from module `List`.
intersperse1 :: a -> [a] -> [a]
intersperse1 _   []           = []
intersperse1 _   [x]          = [x]
intersperse1 sep (x:xs@(_:_)) = x : sep : intersperse1 sep xs

--- Less strict definition.
intersperse2 :: a -> [a] -> [a]
intersperse2 _   []     = []
intersperse2 sep (x:xs) = x : go xs
 where
  go []     = []
  go (y:ys) = sep : y : go ys


-- These operations are not equivalent:
intersperseEquiv = intersperse1 <=> intersperse2
