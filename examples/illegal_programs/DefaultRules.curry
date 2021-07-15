---------------------------------------------------------------------------
-- Here are some examples for problems to be detected by CurryCheck
---------------------------------------------------------------------------

-- Examples for unintended uses of default rules.
-- Note that a default rule for an operation `f` must have the name
-- `f'default` where `f` is a top-level operation.

-- A default rule without an implementation is not allowed.
some'default _ = True

-- It is not allowed to have more than one default rule.
and :: Bool -> Bool -> Bool
and True True = True
and'default True  _ = False
and'default False _ = False

-- Default rules cannot be added to locally defined operations.
land :: Bool -> Bool -> Bool
land x y = g y
 where
  g True = x
  g'default _ = False

---------------------------------------------------------------------------
