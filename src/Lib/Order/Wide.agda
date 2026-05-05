open import 1Lab.Prelude

open import Data.Dec.Base

open import Homotopy.Join

open import Order.Base

module Lib.Order.Wide {ℓ} {A : Type ℓ} ⦃ ahl : H-Level A 2 ⦄ (⊤ : A) where

_≤_ : A → A → Type ℓ
x ≤ y = (x ≡ y) ∗ (y ≡ ⊤)

≤-is-prop : ∀ {x y} → is-prop (x ≤ y)
≤-is-prop = join-is-prop (hlevel 1) (hlevel 1)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans p = join-elim-prop (λ _ → ≤-is-prop) (λ q → subst (_ ≤_) q p) inr

⊤-is-top : ∀ {a b} → a ≤ b → a ≡ ⊤ → a ≡ b
⊤-is-top = join-elim-prop (λ _ → hlevel 1) (λ p _ → p) (λ p q → q ∙ sym p)

≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
≤-antisym p = join-elim-prop (λ _ → hlevel 1) sym (⊤-is-top p)

Wide : Poset ℓ ℓ
Wide .Poset.Ob        = A
Wide .Poset._≤_       = _≤_
Wide .Poset.≤-thin    = ≤-is-prop
Wide .Poset.≤-refl    = inl refl
Wide .Poset.≤-trans   = ≤-trans
Wide .Poset.≤-antisym = ≤-antisym
