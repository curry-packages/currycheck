-- Some tests on floats.

import Float
import Test.Prop

-- Property: the addition operator is commutative
addIsCommutative :: Float -> Float -> Prop
addIsCommutative x y = x +. y -=- y +. x

-- Property: the addition operator is almost associative due to rounding errors
addIsAssociative :: Float -> Float -> Float -> Prop
addIsAssociative x y z = always (almostEqual ((x +. y) +. z) (x +. (y +. z)))

almostEqual :: Float -> Float -> Bool
almostEqual x y = absf (x -. y) < 0.00001
 where
  absf x = if x < 0 then 0.0 -. x else x
