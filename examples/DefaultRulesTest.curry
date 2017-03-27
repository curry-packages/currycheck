{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=defaultrules #-}
{-# OPTIONS_CYMAKE -Wnone #-}

import Test.Prop

-- We test whether our definition of zip with default rules is
-- equivalent to the standard one:

-- zip2 with default rule:
zip2 :: [a] -> [b] -> [(a,b)]
zip2 (x:xs) (y:ys) = (x,y) : zip2 xs ys
zip2'default _ _ = []

zip2_is_zip xs ys = zip2 xs ys -=- Prelude.zip xs ys
