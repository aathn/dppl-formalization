module Lib.Algebra.Field where

open import 1Lab.Prelude hiding (_*_ ; _+_)

open import Algebra.Ring
open import Algebra.Ring.Commutative

record is-field {ℓ} {A : Type ℓ} (1r : A) (_*_ _+_ : A → A → A) : Type ℓ where
  field
    has-is-ring : is-ring 1r _*_ _+_

  open is-ring has-is-ring public

  field
    *-commutes : ∀ {x y} → x * y ≡ y * x
    0≠1        : 0r ≠ 1r
    _[_]⁻¹     : ∀ x → ¬ x ≠ 0r → Σ[ x' ∈ A ] x * x' ≡ 1r

  ring : Σ (Set ℓ) λ X → Ring-on ∣ X ∣
  ring = el A has-is-set , record
    { 1r  = 1r
    ; _*_ = _*_
    ; _+_ = _+_
    ; has-is-ring = has-is-ring
    }

  commutative-ring : Σ (Set ℓ) λ X → CRing-on ∣ X ∣
  commutative-ring = ring .fst , record
    { has-ring-on = ring .snd
    ; *-commutes = *-commutes
    }

record Field-on {ℓ} (A : Type ℓ) : Type ℓ where
  field
    1r : A
    _*_ _+_ : A → A → A
    has-is-field : is-field 1r _*_ _+_

  open is-field has-is-field public
  infixl 25 _*_
  infixl 20 _+_

