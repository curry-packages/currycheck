--------------------------------------------------------------------------
-- Some tests from Sebastian's tutorial on EasyCheck.

-- In order to write a test, we have to import the module Test.Prop:
import Test.Prop

--------------------------------------------------------------------------
-- Deterministic tests:

appendIsAssociative xs ys zs = (xs ++ ys) ++ zs -=- xs ++ (ys ++ zs)

reverseLeavesSingletonUntouched x = reverse [x] -=- [x]

reverseOfNonemptyIsNotNull x xs = reverse (x:xs) `is` (not . null)

reverseAntiDistributesOverAppend xs ys
  = reverse (xs++ys) -=- reverse ys ++ reverse xs

-- Testing non-deterministic operations:

insert :: a -> [a] -> [a]
insert x xs     = x : xs
insert x (y:ys) = y : insert x ys

insertIsNeverNull :: Int -> [Int] -> Prop
insertIsNeverNull x xs = insert x xs `isAlways` (not . null)

insertInsertsAsHead :: Int -> [Int] -> Prop
insertInsertsAsHead x xs = insert x xs ~> x:xs

--------------------------------------------------------------------------
