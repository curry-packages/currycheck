-- Add numbers and define a specific generator for non-negative integers

import Control.SearchTree.Generators
import Test.Prop

sumUp n = if n==0 then 0 else n + sumUp (n-1)

sumUpIsCorrect n = n>=0 ==> sumUp n -=- n * (n+1) `div` 2
sumUpIsCorrectL n = label "MH" $ n>=0 ==> sumUp n -=- n * (n+1) `div` 2
sumUpIsCorrectC n = classify (n>9) "NODIGIT" $ n>=0 ==> sumUp n -=- n * (n+1) `div` 2
sumUpIsCorrectC2 n = classify (n>20) ">20" $ classify (n>9) "NODIGIT" $ n>=0 ==> sumUp n -=- n * (n+1) `div` 2

--genInt = genCons0 0 ||| genCons1 (\n -> 2*(n+1)) genInt
--                    ||| genCons1 (\n -> 2*n+1)   genInt

multIsCommutative x y = classify (x<0 || y<0) "Negative" $ x*y -=- y*x

--addIsCommutative x y = collectAs "ARG" (x,y) $ x*y -=- y*x
