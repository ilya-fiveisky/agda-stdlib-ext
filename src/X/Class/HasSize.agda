{-# OPTIONS --safe #-}
module X.Class.HasSize where

open import Data.List using (List; length)
open import Data.Nat using (ℕ)
open import Level using (Level)

private variable
  ℓ : Level
  A : Set ℓ

record HasSize (A : Set ℓ) : Set ℓ where
  field size : A → ℕ
open HasSize ⦃...⦄ public

instance
  HasSize-ℕ : HasSize ℕ
  HasSize-ℕ .size x = x

  HasSize-List : HasSize (List A)
  HasSize-List .size x = length x

private
  open import Data.List using ([]; _∷_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  _ : size 2 ≡ 2; _ = refl
  _ : size (1 ∷ 2 ∷ []) ≡ 2; _ = refl
