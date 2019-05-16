--- Example from:
--- 
--- Christiansen, J.: Sloth - A Tool for Checking Minimal-Strictness
--- Proc. of the 13th International Symposium on Practical Aspects of
--- Declarative Languages (PADL 2011), pp. 160-174
--- DOI: 10.1007/978-3-642-18378-2_14

import Test.Prop

-- Peano numbers
data Nat = Z | S Nat
 deriving (Eq, Show)

--- Addition
add :: Nat -> Nat -> Nat
add Z      y = y
add (S x ) y = S (add x y)

--- "Standard" definition of multiplication.
mult :: Nat -> Nat -> Nat
mult Z     _ = Z
mult (S x) y = add y (mult x y)

-- An infinite Peano number.
infinity :: Nat
infinity = S infinity

-- mult Z infinity --> Z
-- mult infinity Z --> does not terminate

-- Less strict definition of multiplication.
mult' :: Nat -> Nat -> Nat
mult' Z     _       = Z
mult' (S _) Z       = Z
mult' (S x) y@(S _) = add y (mult' x y)


-- These operations are not equivalent (falsified at 24th test):
multEquiv = mult <=> mult'

-- These operations are not equivalent (falsified at 9th test):
multEquiv'TERMINATE = mult <=> mult'

-- Ground equivalence testing is successful:
multEquiv'GROUND x y = mult x y <~> mult' x y
