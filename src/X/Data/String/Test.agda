{-# OPTIONS  --safe #-}

module X.Data.String.Test where

open import Data.Nat using (_<?_)
open import Data.String using (length)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import X.Data.String.Base

_ : encloseIf ((0 <?_) ∘ length) '[' ']' "x" ≡ "[x]"; _ = refl
_ : encloseIf ((0 <?_) ∘ length) '[' ']' "" ≡ ""; _ = refl
_ : encloseIfChar ' ' '[' ']' "x y" ≡ "[x y]"; _ = refl
_ : doubleQuoteIfSpace "x y" ≡ "\"x y\""; _ = refl
