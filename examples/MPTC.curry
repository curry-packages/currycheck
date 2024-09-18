{-# LANGUAGE MultiParamTypeClasses #-}

import Test.Prop

class Multi a b where
  binOp :: a -> b -> Int
  
instance Multi Int Int where
  binOp = (+)
  
-- Property: the implementation of `binOp` on two integers is commutative
isCommutative :: Int -> Int -> Prop
isCommutative x y = x `binOp` y -=- y `binOp` x
