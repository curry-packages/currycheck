---------------------------------------------------------------------------
-- Here are some examples for problems detected by CurryCheck
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- The direct use primitives to implement functional patterns is
-- not allowed since their intended use is not ensured.

testNonStrictUniv x | 3 =:<= x = True  -- not allowed!

---------------------------------------------------------------------------
