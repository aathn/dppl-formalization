open import 1Lab.Prelude

open import Data.Dec.Base

open import Lib.Homotopy.Join

open import Order.Base

module Lib.Order.Wide {ℓ} {A : Type ℓ} ⦃ ahl : H-Level A 2 ⦄ (⊤ : A) where

_≤_ : A → A → Type ℓ
x ≤ y = (x ≡ y) ∗ (y ≡ ⊤)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans p q = case q of λ where
  (inl q) → subst (_ ≤_) q p
  (inr q) → inr q

⊤-is-top : ∀ {a b} → a ≤ b → a ≡ ⊤ → a ≡ b
⊤-is-top p = case p of λ where
  (inl p) _ → p
  (inr p) q → q ∙ sym p

≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
≤-antisym p q = case q of λ where
  (inl q) → sym q
  (inr q) → ⊤-is-top p q

Wide : Poset ℓ ℓ
Wide .Poset.Ob        = A
Wide .Poset._≤_       = _≤_
Wide .Poset.≤-thin    = hlevel 1
Wide .Poset.≤-refl    = inl refl
Wide .Poset.≤-trans   = ≤-trans
Wide .Poset.≤-antisym = ≤-antisym
