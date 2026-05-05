open import 1Lab.Prelude hiding (_*_ ; _+_)

open import Lib.Algebra.OrderedRing
open import Lib.Algebra.Field

open import Order.Diagram.Lub
open import Order.Base

module Lib.Algebra.Reals where

-- We characterize the real numbers as the ordered field with the
-- least-upper-bound property.
record is-reals {o ℓ} (ℝ : Poset o ℓ) (1r : ⌞ ℝ ⌟) (_*_ _+_ : ⌞ ℝ ⌟ → ⌞ ℝ ⌟ → ⌞ ℝ ⌟) : Type (lsuc o ⊔ ℓ) where
  field
    has-is-field : is-field 1r _*_ _+_

  open is-field has-is-field public

  field
    has-is-ordered-ring : is-ordered-ring ℝ (ring .snd)

  open is-ordered-ring has-is-ordered-ring public hiding (ring)

  -- Any subset which is inhabited and has an upper bound has a
  -- supremum.
  is-valid-sup : (I : Type o) → (I → ⌞ ℝ ⌟) → Type (o ⊔ ℓ)
  is-valid-sup I xs = ∥ I ∥ × ∃[ x ∈ ℝ ] ∀ i → xs i ≤ x

  field
    sup[_,_]   : {I : Type o} (xs : I → ⌞ ℝ ⌟) → is-valid-sup I xs → ⌞ ℝ ⌟
    sup-is-lub : {I : Type o} (xs : I → ⌞ ℝ ⌟) (valid : is-valid-sup I xs) → is-lub ℝ xs sup[ xs , valid ]

  ordered-ring : Σ (Poset o ℓ) Ordered-ring-on
  ordered-ring = ℝ , record
    { has-ring-on = ring .snd
    ; has-is-ordered-ring = has-is-ordered-ring
    }

  reals-field : Σ (Set o) λ X → Field-on ∣ X ∣
  reals-field = el ⌞ ℝ ⌟ has-is-set , record
    { 1r  = 1r
    ; _*_ = _*_
    ; _+_ = _+_
    ; has-is-field = has-is-field
    }

record Reals-on {o ℓ} (ℝ : Poset o ℓ) : Type (lsuc o ⊔ ℓ) where
  field
    1r : ⌞ ℝ ⌟
    _*_ _+_ : ⌞ ℝ ⌟ → ⌞ ℝ ⌟ → ⌞ ℝ ⌟
    has-is-reals : is-reals ℝ 1r _*_ _+_

  open is-reals has-is-reals public
  infixl 25 _*_
  infixl 20 _+_

Reals : ∀ o ℓ → Type (lsuc (o ⊔ ℓ))
Reals o ℓ = Σ (Poset o ℓ) Reals-on

Reals₀ : Type₁
Reals₀ = Reals lzero lzero

module Reals {o ℓ} (R : Reals o ℓ) where
  open Reals-on (R .snd) public

  ℝ : Type o
  ℝ = ⌞ R .fst ⌟

module Interval {o ℓ} (R : Reals o ℓ) where
  open Reals R
  open Reasoning (ordered-ring .snd)

  𝕀 : Type _
  𝕀 = Σ[ r ∈ ℝ ] 0r ≤ r × r ≤ 1r

  0i : 𝕀
  0i = 0r , ≤-refl , 0≤1

  1i : 𝕀
  1i = 1r , 0≤1 , ≤-refl
