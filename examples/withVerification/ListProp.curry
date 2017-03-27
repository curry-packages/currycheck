--- This module contains some contracts for list operations.

import Test.Prop

-- The well-known list concatenation. We give it another name,
-- otherwise we cannot specify contracts for it.
append :: [a] -> [a] -> [a]
append xs ys = xs ++ ys

-- Postcondition: append add length of input lists.
append'post xs ys zs = length xs + length ys == length zs

-- We formulate the postcondition as a property:
appendAddLengths xs ys = length xs + length ys -=- length (append xs ys)
