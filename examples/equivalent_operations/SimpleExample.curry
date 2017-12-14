import Test.Prop

-- This is an example which shows the "non-referentiality" of Curry (according
-- to [Bacci et al. PPDP'12]), i.e., it shows that two operations, which
-- compute the same values, might compute different results in larger
-- contexts:

data AB = A | B

data C = C AB

h A = A

g x = C (h x)

g' A = C A


-- The computed result equivalence of g and g' on ground values
-- always holds, i.e., g and g' always compute same values:
g_and_g' :: AB -> Prop
g_and_g' x = g x <~> g' x

-- The contextual equivalence of g and g' does not hold:
g_equiv_g' = g <=> g'
