---------------------------------------------------------------------------
-- Here are some examples for problems to be detected by CurryCheck
---------------------------------------------------------------------------

-- Examples for intended and unintended uses of `Prelude.DET` type synonym.
-- Note that `DET` should only be used to mark the result type of a
-- top-level operation.

-- Ok (but superfluous):
detok :: Bool -> Bool ->DET Bool
detok x _ = x

-- Not allowed: DET must occur in the result type
deterr1 :: DET Bool -> Bool
deterr1 x = x

-- Not allowed: DET must occur outermost in the result type
deterr2 :: Bool -> [DET Bool]
deterr2 x = [x]

-- Not allowed: DET can only be used for top-level operations
deterr3 :: Bool -> Bool
deterr3 x = f x
 where
  f :: Bool -> DET Bool
  f x = x

---------------------------------------------------------------------------
