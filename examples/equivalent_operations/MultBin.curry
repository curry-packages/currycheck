--- Example from:
--- 
--- Christiansen, J.: Sloth - A Tool for Checking Minimal-Strictness
--- Proc. of the 13th International Symposium on Practical Aspects of
--- Declarative Languages (PADL 2011), pp. 160-174
--- DOI: 10.1007/978-3-642-18378-2_14

import Test.Prop

-- from package BinInt:

--- Algebraic data type to represent natural numbers.
--- @cons IHi - most significant bit
--- @cons O   - multiply with 2
--- @cons I   - multiply with 2 and add 1
data Nat = IHi | O Nat | I Nat
 deriving (Eq,Show)

--- Successor, O(n)
succ :: Nat -> Nat
succ IHi    = O IHi        -- 1       + 1 = 2
succ (O bs) = I bs         -- 2*n     + 1 = 2*n + 1
succ (I bs) = O (succ bs)  -- 2*n + 1 + 1 = 2*(n+1)

--- Addition, O(max (m, n))
(+^) :: Nat -> Nat -> Nat
IHi +^ y   = succ y           -- 1  +  n   = n + 1
O x +^ IHi = I x              -- 2*n + 1   = 2*n + 1
O x +^ O y = O (x +^ y)       -- 2*m + 2*n = 2*(m+n)
O x +^ I y = I (x +^ y)
I x +^ IHi = O (succ x)
I x +^ O y = I (x +^ y)
I x +^ I y = O (succ x +^ y)

--- Multiplication, O(m*n)
mult :: Nat -> Nat -> Nat
mult IHi   y = y
mult (O x) y = O (mult x y)
mult (I x) y = y +^ (O (mult x y))

--- Multiplication, O(m*n)
mult' :: Nat -> Nat -> Nat
mult' IHi   y = y
mult' (O x) y = O (mult' x y)
mult' (I x) y = (O (mult' y x)) +^ y



-- These operations are not equivalent (falsified at 1041th test):
multEquiv = mult <=> mult'

-- These operations are not equivalent (falsified at 42th test):
multEquiv'TERMINATE = mult <=> mult'

-- Ground equivalence testing is successful:
multEquiv'GROUND x y = mult x y <~> mult' x y
