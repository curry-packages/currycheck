import Test.Prop

-- This is an example from
--
-- G. Bacci, M. Comini, M.A. Feliu, A. Villanueva:
-- Automatic Synthesis of Specifications for First Order Curry
-- Proc. Principles and Practice of Declarative Programming (PPDP'12),
-- ACM Press, pp. 25-34
--
-- It shows that two operations, which compute the same values,
-- might compute different results in larger contexts.
-- This example is also used in the introduction of the paper
-- explaining the equivalence checking features implemented in CurryCheck:
--
-- Antoy, S., Hanus, M.:
-- Equivalence Checking of Non-deterministic Operations
-- Proc. 14th Int. Symp. on Functional and Logic Programming (FLOPS 2018),
-- Springer LNCS 10818, pp. 149-165, 2018

data AB = A | B
 deriving (Eq,Show)

data C = C AB
 deriving (Eq,Show)

h :: AB -> AB
h A = A

f :: AB -> C
f x = C (h x)

g :: AB -> C
g A = C A


-- The computed result equivalence of f and g on ground values
-- always holds, i.e., f and g always compute same values.
-- Since the domain is finite, this property is actually proved by CurryCheck.
f_and_g :: AB -> Prop
f_and_g x = f x <~> g x

-- The contextual equivalence of f and g  does not hold.
-- The counter-example is found by CurryCheck with the 2nd test
-- (or with the 1st test when option "--equivalence=autoselect" is used).
f_equiv_g :: Prop
f_equiv_g = f <=> g
