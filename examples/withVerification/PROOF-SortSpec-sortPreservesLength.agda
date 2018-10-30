-- Agda program using the Iowa Agda library

open import bool

module PROOF-SortSpec-sortPreservesLength
  (Choice : Set)
  (choose : Choice → 𝔹)
  (lchoice : Choice → Choice)
  (rchoice : Choice → Choice)
  where

open import eq
open import nat
open import list
open import maybe

---------------------------------------------------------------------------
-- Translated Curry operations:

insert : ℕ → 𝕃 ℕ → 𝕃 ℕ
insert x [] = x :: []
insert y (z :: u) = if y ≤ z then y :: (z :: u) else z :: (insert y u)

sort : 𝕃 ℕ → 𝕃 ℕ
sort [] = []
sort (x :: y) = insert x (sort y)

---------------------------------------------------------------------------

insertIncLength : (x : ℕ) → (xs : 𝕃 ℕ)
                → length (insert x xs) ≡ suc (length xs)
insertIncLength x [] = refl
insertIncLength x (y :: ys) with (x ≤ y)
... | tt = refl
... | ff rewrite insertIncLength x ys = refl

sortPreservesLength : (xs : 𝕃 ℕ) → length (sort xs) ≡ length xs
sortPreservesLength [] = refl
sortPreservesLength (x :: xs)
 rewrite insertIncLength x (sort xs) | sortPreservesLength xs = refl

---------------------------------------------------------------------------
