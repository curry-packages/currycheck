import Test.Prop

revrev :: [a] -> [a]
revrev xs = reverse (reverse xs)

-- Test: is double reverse equivalent to the identity?
-- This is not the case if both are applied to the context
--     head (... (1:failed))
revrevid'TERMINATE = revrev <=> id
