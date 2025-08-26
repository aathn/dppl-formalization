open import 1Lab.Prelude

open import Order.Base
open import Data.Dec.Base

module Lib.Order.Wide {ℓ} {A : Type ℓ} ⦃ hl : H-Level A 2 ⦄ (⊤ ⊥ : A) (⊤≠⊥ : ⊤ ≠ ⊥) where

  data _≤_ : A → A → Type ℓ where
    x≤⊤ : ∀ {x} → x ≤ ⊤
    ⊥≤x : ∀ {x} → ⊥ ≤ x
    ≤-refl : ∀ {x} → x ≤ x
    squash : ∀ {x y} → is-prop (x ≤ y)

  ≤-is-prop : ∀ {a b} → is-prop (a ≤ b)
  ≤-is-prop = squash

  ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans x≤⊤ x≤⊤    = x≤⊤
  ≤-trans x≤⊤ ⊥≤x    = absurd (⊤≠⊥ refl)
  ≤-trans x≤⊤ ≤-refl = x≤⊤
  ≤-trans ⊥≤x    b≤c = ⊥≤x
  ≤-trans ≤-refl b≤c = b≤c
  ≤-trans x≤⊤ (squash b≤c b≤c' i) =
    squash (≤-trans x≤⊤ b≤c) (≤-trans x≤⊤ b≤c') i
  ≤-trans (squash a≤b a≤b' i) b≤c =
    squash (≤-trans a≤b b≤c) (≤-trans a≤b' b≤c) i

  ≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
  ≤-antisym x≤⊤ x≤⊤    = refl
  ≤-antisym x≤⊤ ⊥≤x    = absurd (⊤≠⊥ refl)
  ≤-antisym x≤⊤ ≤-refl = refl
  ≤-antisym ⊥≤x ⊥≤x    = refl
  ≤-antisym ⊥≤x x≤⊤    = absurd (⊤≠⊥ refl)
  ≤-antisym ⊥≤x ≤-refl = refl
  ≤-antisym ≤-refl H≤' = refl
  ≤-antisym {a} x≤⊤ (squash H≤ H≤' i) =
    hlevel 2 _ _ (≤-antisym x≤⊤ H≤) (≤-antisym x≤⊤ H≤') i
  ≤-antisym ⊥≤x (squash H≤ H≤' i) =
    hlevel 2 _ _ (≤-antisym ⊥≤x H≤) (≤-antisym ⊥≤x H≤') i
  ≤-antisym (squash H≤ H≤₁ i) H≤' =
    hlevel 2 _ _ (≤-antisym H≤ H≤') (≤-antisym H≤₁ H≤') i

  instance
    ≤-dec : ⦃ Discrete A ⦄ → ∀ {a b} → Dec (a ≤ b)
    ≤-dec ⦃ x ⦄ {a} {b} with b ≡? ⊤
    ... | yes p = yes (subst (a ≤_) (sym p) x≤⊤)
    ... | no ¬p with a ≡? ⊥
    ... | yes q = yes (subst (_≤ b) (sym q) ⊥≤x)
    ... | no ¬q with a ≡? b
    ... | yes s = yes (subst (a ≤_) s ≤-refl)
    ... | no ¬s = no ¬a≤b where
      ¬a≤b : _
      ¬a≤b x≤⊤    = absurd (¬p refl)
      ¬a≤b ⊥≤x    = absurd (¬q refl)
      ¬a≤b ≤-refl = absurd (¬s refl)
      ¬a≤b (squash a≤b a≤b' i) = hlevel 1 (¬a≤b a≤b) (¬a≤b a≤b') i

  Wide : Poset ℓ ℓ
  Wide .Poset.Ob = A
  Wide .Poset._≤_ = _≤_
  Wide .Poset.≤-thin = ≤-is-prop
  Wide .Poset.≤-refl = ≤-refl
  Wide .Poset.≤-trans = ≤-trans
  Wide .Poset.≤-antisym = ≤-antisym
