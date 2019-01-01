---------------------------------------------------------------------------
-- Here are some examples for problems to be detected by CurryCheck
---------------------------------------------------------------------------

import Control.SetFunctions

---------------------------------------------------------------------------
-- Detection of unintended uses of set functions and functional pattern unif.

test1 x | 3 =:<= x = True  -- not allowed!

test2 = set2 (++) [] [42]  -- ok

test3 = set0 ([]++[42])    -- illegal!

test4 = set0 failed        -- ok

test5 = set1 (\x->x) (1?2) -- unintended!

test6 x = set1 f x         -- not allowed since f is not a top-level function
 where f y = y

test7 xs = set1 (++) xs    -- not allowed since (++) has arity 2

---------------------------------------------------------------------------
-- Examples for intended and unintended uses of Prelude.DET type synonym:

-- Ok (but superfluous):
detok :: Bool -> Bool ->DET Bool
detok x _ = x

deterr1 :: DET Bool -> Bool
deterr1 x = x

deterr2 :: Bool -> [DET Bool]
deterr2 x = [x]

deterr3 :: Bool -> Bool
deterr3 x = f x
 where
  f :: Bool -> DET Bool
  f x = x

---------------------------------------------------------------------------
-- Examples for unintended uses of contracts:

some'pre _ = True

some'post _ _ = True

some'spec x = x

k'spec x = x
k x _ = x

inc :: Int -> Int
inc n = n + 1

-- Illegal contract types:
inc'pre x = x

inc'post x y = x+y

---------------------------------------------------------------------------
