-- Agda program using the Iowa Agda library

open import bool

module PROOF-appendAddLengths
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

++ : {a : Set} → 𝕃 a → 𝕃 a → 𝕃 a
++ [] x = x
++ (y :: z) u = y :: (++ z u)

append : {a : Set} → 𝕃 a → 𝕃 a → 𝕃 a
append x y = ++ x y

---------------------------------------------------------------------------

appendAddLengths : {a : Set} → (x : 𝕃 a) → (y : 𝕃 a)
                 → ((length x) + (length y)) ≡ (length (append x y))
appendAddLengths [] y = refl
appendAddLengths (x :: xs) y rewrite appendAddLengths xs y = refl

---------------------------------------------------------------------------
