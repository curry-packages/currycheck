module Proof-DetOps-last-is-deterministic where

-- Show that last is a deterministic operation.
-- The property to show is:
--
-- l == l1 ++ [x1] and l == l2 ++ [x2]  implies x1 == x2
--
-- Here we show the simplified property
--
--  l1 ++ [x1] == l2 ++ [x2]  implies x1 == x2
--
-- The initial property can be derived from this one by by symmetry
-- and transitivity of Boolean equality.

open import bool
open import bool-thms
open import bool-thms2
open import list
open import nat
open import eq

-- Auxiliary statements: an empty list cannot be equal to a list with
-- an element at the end:
nonemptylast :  ∀ (l : 𝕃 ℕ)(x : ℕ) → =𝕃 _=ℕ_ [] (l ++ [ x ]) ≡ ff
nonemptylast [] x = refl
nonemptylast (z :: l) x = refl

nonemptylastr :  ∀ (l : 𝕃 ℕ)(x : ℕ) → =𝕃 _=ℕ_ (l ++ [ x ]) [] ≡ ff
nonemptylastr [] x = refl
nonemptylastr (z :: l) x = refl

-- Main property formulated as Boolean implication:
lasteqp : ∀ (l1 l2 : 𝕃 ℕ)(x1 x2 : ℕ)
            → (=𝕃 _=ℕ_ (l1 ++ [ x1 ]) (l2 ++ [ x2 ])) imp (x1 =ℕ x2) ≡ tt
lasteqp [] [] x1 x2 rewrite &&-tt (x1 =ℕ x2) | imp-same (x1 =ℕ x2) = refl
lasteqp [] (x :: l2) x1 x2
  rewrite nonemptylast l2 x2 | &&-ff (x1 =ℕ x) = refl
lasteqp (x :: l1) [] x1 x2
  rewrite nonemptylastr l1 x1 | &&-ff (x =ℕ x2) = refl
lasteqp (z1 :: l1) (z2 :: l2) x1 x2 with (z1 =ℕ z2)
lasteqp (z1 :: l1) (z2 :: l2) x1 x2 | tt
  rewrite lasteqp l1 l2 x1 x2 = refl
lasteqp (z1 :: l1) (z2 :: l2) x1 x2 | ff = refl

-- Main property formulated as propositional implication:
lasteq : ∀ (l1 l2 : 𝕃 ℕ)(x1 x2 : ℕ)
            → =𝕃 _=ℕ_ (l1 ++ [ x1 ]) (l2 ++ [ x2 ]) ≡ tt
            → x1 =ℕ x2 ≡ tt
lasteq l1 l2 x1 x2 p = imp-mp (lasteqp l1 l2 x1 x2) p

