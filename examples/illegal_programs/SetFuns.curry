---------------------------------------------------------------------------
-- Here are some examples for problems detected by CurryCheck
---------------------------------------------------------------------------

import Control.Search.SetFunctions

-- Detection of unintended uses of set functions.
-- Note that `setN` must be applied to an `N`-ary top-level operation
-- but not to locally defined operations, lambda abstractions, etc.

test2 = set2 (++) [] [42]  -- ok

test3 = set0 ([]++[42])    -- illegal!

test4 = set0 failed        -- ok

test5 = set1 (\x->x) (1?2) -- unintended!

test6 x = set1 f x         -- not allowed since f is not a top-level function
 where f y = y

test7 xs = set1 (++) xs    -- not allowed since (++) has arity 2

---------------------------------------------------------------------------
