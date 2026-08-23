{-# OPTIONS  --safe #-}

module X.Data.String where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Char using (Char)
open import Data.String using (String; between; fromChar; toList)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable.Core using (does)
open import Relation.Unary using (Decidable; Pred)

import Data.Char.Properties as Char using (_≟_)
open import Data.List.Membership.DecPropositional Char._≟_
open import Relation.Nullary.Decidable.Core using (does)

-- Encloses string `s` with `encl` and `encr` characters if `s` satisfies P predicate.
encloseIf : {P : Pred String 0ℓ} → Decidable P → Char → Char → String → String
encloseIf p encl encr s = if does (p s) then between (fromChar encl) (fromChar encr) s else s

-- Encloses string `s` with `encl` and `encr` characters if it contains `ifc` character.
encloseIfChar : Char → Char → Char → String → String
encloseIfChar ifc encl encr s = encloseIf ((ifc ∈?_) ∘ toList) encl encr s

doubleQuoteIfSpace = encloseIfChar ' ' '"' '"'

open import Data.Nat using (_<?_)
open import Data.String using (length)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  _ : encloseIf ((0 <?_) ∘ length) '[' ']' "x" ≡ "[x]"; _ = refl
  _ : encloseIf ((0 <?_) ∘ length) '[' ']' "" ≡ ""; _ = refl
  _ : encloseIfChar ' ' '[' ']' "x y" ≡ "[x y]"; _ = refl
  _ : doubleQuoteIfSpace "x y" ≡ "\"x y\""; _ = refl
