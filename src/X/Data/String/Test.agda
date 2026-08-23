{-# OPTIONS  --safe #-}

module X.Data.String.Test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import X.Data.String.Base

_ : doubleQuoteIfSpace "x y" ≡ "\"x y\""; _ = refl
