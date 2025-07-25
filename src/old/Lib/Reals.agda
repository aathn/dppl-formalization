module Lib.Reals where

open import Lib.Prelude hiding (_+_)
open import Lib.OrderedField

open import Algebra using (Op₁ ; Op₂)

upper-bound : {a ℓ ℓ′ : Level} {A : Set a} (_≲_ : Rel A ℓ′) (S : ℙ A ℓ) → ℙ A _
upper-bound _≲_ S r = ∀ s → S s → s ≲ r

least-upper-bound : {a ℓ ℓ′ : Level} {A : Set a} (_≲_ : Rel A ℓ′) (S : ℙ A ℓ) → ℙ A _
least-upper-bound _≲_ S r = upper-bound _≲_ S r × ∀ s → upper-bound _≲_ S r → r ≲ s

record IsReals
  {a ℓ ℓ′} {A : Set a} (ℓ″ : Level) (_≈_ : Rel A ℓ) (_≲_ : Rel A ℓ′)
  (+ * : Op₂ A) (- : Op₁ A) (0ᴿ 1ᴿ : A)
  : Set (lsuc (a ⊔ ℓ ⊔ ℓ′ ⊔ ℓ″))
  where
  field
    isOrderedField : IsOrderedField _≈_ _≲_ + * - 0ᴿ 1ᴿ
    hasLubProperty : ∀ (S : ℙ A ℓ″) → ∃ S → ∃ (least-upper-bound _≲_ S)

  open IsOrderedField isOrderedField public

record Reals a ℓ ℓ′ ℓ″ : Set (lsuc (a ⊔ ℓ ⊔ ℓ′ ⊔ ℓ″)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  infix  4 _≲_
  field
    ℝ       : Set a
    _≈_     : Rel ℝ ℓ
    _≲_     : Rel ℝ ℓ′
    _+_     : Op₂ ℝ
    _*_     : Op₂ ℝ
    -_      : Op₁ ℝ
    0ᴿ      : ℝ
    1ᴿ      : ℝ
    isReals : IsReals ℓ″ _≈_ _≲_ _+_ _*_ -_ 0ᴿ 1ᴿ

  open IsReals isReals public

  orderedField : OrderedField _ _ _
  orderedField = record { isOrderedField = isOrderedField }

  _≲?_ : ℝ → ℝ → 𝔹
  r ≲? s with total r s
  ... | ι₁ _ = true
  ... | ι₂ _ = false

module Interval {a ℓ ℓ′ ℓ″} (R : Reals a ℓ ℓ′ ℓ″) where
  open Reals R
  open Properties orderedField

  𝕀 : Set (a ⊔ ℓ′)
  𝕀 = ∃ λ r → 0ᴿ ≲ r × r ≲ 1ᴿ

  0ᴵ : 𝕀
  0ᴵ = 0ᴿ , ≲-refl , 0≲1

  1ᴵ : 𝕀
  1ᴵ = 1ᴿ , 0≲1 , ≲-refl

Reals₀ : Set₁
Reals₀ = Reals ℓ₀ ℓ₀ ℓ₀ ℓ₀
