module Properties.Util (ℝ : Set) where

-- Utility lemmas

open import Lib.Prelude

open import Function using (_$_)
open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.Product using (∃-syntax)

all-⊎
  : ∀ {n} {A B : Fin n → Set}
  → (∀ i → A i ⊎ B i)
  → -------------------------------------------------------
    (∀ i → A i) ⊎ ∃[ j ] B j × ∀ (i : Fin n) → i <ꟳ j → A i

all-⊎ {zero} f = ι₁ λ()
all-⊎ {n +1} f =
  case (f zero) λ
    { (ι₁ Ha) →
      case (all-⊎ (f ∘ succ)) λ
        { (ι₁ Has) → ι₁ $ λ { zero → Ha ; (succ n) → Has n }
        ; (ι₂ (j , Hb , Has)) → ι₂ $
          _ , Hb , λ { zero _ → Ha ; (succ n) H≤ → Has n (≤-1 H≤) }
        }
    ; (ι₂ Hb) → ι₂ $ _ , Hb , λ _ ()
    }

