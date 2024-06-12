{-# LANGUAGE MultiParamTypeClasses #-}

import Test.Prop

class Multi a b where
  operation :: a -> b -> Int
  
instance Multi Int Int where
  operation = (+)
  
someTest :: Float -> Float -> Prop
someTest x y = x + y -=- y + x
