-- Vectors defined as indexed Containers.

{-# OPTIONS --safe #-}

module X.Data.Vec.Container where

open import Data.Container.Indexed using (Container; next; ⟦_⟧)
  renaming (Command to Shape; Response to Position)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Functional using () renaming ([] to []ᶠ; _∷_ to _∷ᶠ_)
open import Function using (_$_; const)
open import Level using (0ℓ)
open import Relation.Unary using (Pred)

data VectorS : ℕ → Set where
  nil : VectorS zero
  cons : ∀ n → VectorS (suc n)

VectorC : Container ℕ ℕ 0ℓ 0ℓ
VectorC .Shape = VectorS
VectorC .Position nil = Fin zero
VectorC .Position (cons n) = Fin (suc n)
VectorC .next nil = λ ()
VectorC .next (cons n) = const (suc n)

module _ {ℓ} (A : Set ℓ) where
  Vector = ⟦ VectorC ⟧ $ const A

module _ {ℓ} {A : Set ℓ} where
  [] : Vector A 0
  [] = nil , []ᶠ

  infixr 3 _∷_
  _∷_ : ∀ {n} → A → Vector A n → Vector A (suc n)
  (a ∷ (nil , _)) = cons zero , a ∷ᶠ []ᶠ
  (a ∷ (cons n , as)) = cons (suc n) , a ∷ᶠ as

private
  _ : Vector ℕ 3
  _ = 1 ∷ 2 ∷ 3 ∷ []
