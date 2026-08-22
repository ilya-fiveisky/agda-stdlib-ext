{-# OPTIONS --safe #-}
module X.System.Process.ToCmdLineArgs.Test where

open import Data.Integer using (ℤ; +_)
open import Data.Integer.Show using (show)
open import Data.List using (List; []; [_]; _∷_)
open import Function using (_∘_; _∋_; _$_)
open import X.System.Process.ToCmdLineArgs.Base

instance
  ToCmdLineArgs-ℤ = mkToCmdLineArgs $ [_] ∘ show
  ToCmdLineArgs-List[ℤ] = ToCmdLineArgs (List ℤ) ∋ ToCmdLineArgs-List

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

_ : toCmdLineArgs (+ 1 ∷ + 2 ∷ []) ≡ "1" ∷ "2" ∷ []; _ = refl
