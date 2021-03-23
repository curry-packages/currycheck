{-# OPTIONS_FRONTEND -F --pgmF=currypp --optF=defaultrules #-}
{-# OPTIONS_FRONTEND -Wnone #-}

import Control.SetFunctions -- required by default rules
import Test.Prop

-- We test whether our definition of zip with default rules is
-- equivalent to the standard one:

-- zip2 with default rule:
zip2 :: (Data a, Data b) => [a] -> [b] -> [(a,b)]
zip2 (x:xs) (y:ys) = (x,y) : zip2 xs ys
zip2'default _ _ = []

zip2_is_zip xs ys = zip2 xs ys -=- Prelude.zip xs ys
