open import 1Lab.Prelude

open import Data.Sum

open import Homotopy.Join

module Lib.Homotopy.Join where

open Homotopy.Join public
open Data.Sum public using (inl ; inr)

instance
  H-Level-Join-prop
    : ∀ {n} {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → ⦃ H-Level A 1 ⦄ → ⦃ H-Level B 1 ⦄ → H-Level (A ∗ B) (suc n)
  H-Level-Join-prop = prop-instance (join-is-prop (hlevel 1) (hlevel 1))

instance
  Inductive-Join-prop
    : ∀ {ℓA ℓB ℓ' ℓm} {A : Type ℓA} {B : Type ℓB} {P : A ∗ B → Type ℓ'}
    → ⦃ i : Inductive (∀ x → P ([ inl , inr ] x)) ℓm ⦄
    → ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄
    → Inductive (∀ x → P x) ℓm
  Inductive-Join-prop ⦃ i ⦄ ⦃ j ⦄ = record
    { methods = i .Inductive.methods
    ; from    = λ f → join-elim-prop (λ _ → hlevel 1)
      (λ x → i .Inductive.from f (inl x))
      (λ y → i .Inductive.from f (inr y))
    }
