import Test.Prop

revrev :: [a] -> [a]
revrev xs = reverse (reverse xs)

-- Test: is double reverse equivalent to the identity?
-- This is not the case if both are applied to the context
--     head (... (1:failed))

-- Equivalence falsified by 13th test:
revrevid = revrev <=> id

-- Equivalence falsified by 3rd test:
revrevid'TERMINATE = revrev <=> id

-- Ground equivalence not falsified:
revrevid'GROUND xs = revrev xs <~> id xs
