{-# OPTIONS  --safe #-}

module X.Data.String where

open import Data.Bool using (if_then_else_)
open import Data.Char using (Char)
open import Data.String using (String; between; fromChar; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (does)

import Data.Char.Properties as Char using (_≟_)
open import Data.List.Membership.DecPropositional Char._≟_
open import Relation.Nullary.Decidable.Core using (does)

-- Encloses string `s` with `enc` character if it contains `ifc` character.
encloseIf : Char → Char → String → String
encloseIf ifc enc s = if does (ifc ∈? toList s) then between (fromChar enc) (fromChar enc) s else s

doubleQuoteIfSpace = encloseIf ' ' '"'

_ : doubleQuoteIfSpace "x y" ≡ "\"x y\""; _ = refl
