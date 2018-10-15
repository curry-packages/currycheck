-- Some tests involving higher-order functions so that also
-- functional values are generated.

import Test.Prop

-- Naive list reverse.
rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

-- Map a function on all elements of a list.
map :: (a->b) -> [a] -> [b]
map _ []        = []
map f (x:xs)    = f x : map f xs

revMap f xs = rev (map f xs) <~> map f (rev xs)

mapMap f g xs = map (f . g) xs <~> map f (map g xs)
