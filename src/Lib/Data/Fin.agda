module Lib.Data.Fin where

open import Lib.Data.Nat using (module NatOrd)

open import 1Lab.Prelude
open import Data.Fin.Base using (Fin ; _<_ ; fzero ; fsuc ; fin-view ; zero ; suc)
open import Data.Sum.Base using (_⊎_ ; inl ; inr)

Fin-search-⊎ :
  {n : Nat}
  {A B : Fin n → Type}
  (_ : ∀ i → A i ⊎ B i)
  → --------------------------------------------------------------
  (∀ i → A i) ⊎ (Σ[ j ∈ Fin n ] B j × ∀ (i : Fin n) → i < j → A i)

Fin-search-⊎ {zero} f = inl λ()
Fin-search-⊎ {suc n} f with f fzero | Fin-search-⊎ (f ∘ fsuc)
... | inr Hb | _ = inr $ _ , Hb , λ _ ()
... | inl Ha | inl Has = inl λ i → case fin-view i of λ where
  zero    → Ha
  (suc i) → Has i
... | inl Ha | inr (j , Hb , Has) = inr $ _ , Hb , λ i → case fin-view i of λ where
  zero _                  → Ha
  (suc i) (NatOrd.s≤s H≤) → Has i H≤
