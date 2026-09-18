-- Test for multi-parameter type classes with functional dependencies and
-- flexible instances.
-- Note that the LANGUAGE pragmas must be also put into the generated
-- test public module.

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

import Test.Prop

-- Generalization of list-like structures.
class ListLike l e | l -> e where
  nil :: l
  cons :: e -> l -> l
  uncons :: l -> Maybe (e, l)

-- Permutation on a list-like structure.
permutations :: ListLike l e => l -> l
permutations zs = case uncons zs of Nothing      -> nil
                                    Just (x, xs) -> ins x (permutations xs)
 where ins e ys = case uncons ys of
         Nothing      -> cons e nil
         Just (x, xs) -> cons e (cons x xs) ? cons x (ins e xs)

-- Instance for standard lists.
instance ListLike [a] a where
  nil = []
  cons = (:)
  uncons []     = Nothing
  uncons (x:xs) = Just (x,xs)

testPermList123 :: Prop
testPermList123 = permutations [1,2,3] <~>
                  ([1,2,3] ? [2,1,3] ? [2,3,1] ? [1,3,2] ? [3,1,2] ? [3,2,1])

-- Instance for my lists.
data List a = Nil | Cons a (List a)
 deriving (Eq,Show)

instance ListLike (List a) a where
  nil = Nil
  cons = Cons
  uncons Nil         = Nothing
  uncons (Cons x xs) = Just (x,xs)

testPermMyList123 :: Prop
testPermMyList123 = permutations (Cons 1 (Cons 2 Nil)) <~>
                    (Cons 1 (Cons 2 Nil) ? Cons 2 (Cons 1 Nil))

