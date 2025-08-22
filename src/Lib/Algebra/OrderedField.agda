module Lib.Algebra.OrderedField where

open import Lib.Algebra.Field

open import 1Lab.Prelude hiding (_+_ ; _*_)
open import Order.Base
open import Order.Total

record is-ordered-field {o ℓ} (P : Poset o ℓ)
  (1f : ⌞ P ⌟) (_+_ _*_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟) : Type (o ⊔ ℓ)
  where
  field
    has-is-field : is-field 1f _+_ _*_
    has-is-total-order : is-total-order P

  open is-field has-is-field public
  open is-total-order has-is-total-order public

  field
    +-preserves-≤r  : (a b c : ⌞ P ⌟) → a ≤ b → (a + c) ≤ (b + c)
    *-preserves-pos : (a b : ⌞ P ⌟) → 0f ≤ a → 0f ≤ b → 0f ≤ (a * b)

record Ordered-field-on {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  field
    1f : ⌞ P ⌟
    _*_ _+_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
    has-is-ordered-field : is-ordered-field P 1f _*_ _+_

  open is-ordered-field has-is-ordered-field public
  infixl 25 _*_
  infixl 20 _+_
