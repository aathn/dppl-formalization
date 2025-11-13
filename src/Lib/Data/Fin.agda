module Lib.Data.Fin where

open import 1Lab.Prelude
open import Data.Fin.Base
open import Data.Sum.Base using (_⊎_ ; inl ; inr ; ⊎-map)
open import Data.Nat using (s≤s)
open import Data.Nat.Properties using (+-≤l)

private variable
  n m : Nat


Fin-search-⊎ :
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
  zero _           → Ha
  (suc i) (s≤s H≤) → Has i H≤

split-+-inl
  : {i : Fin (m + n)} {j : Fin m}
  → split-+ i ≡ᵢ inl j → inject (+-≤l _ _) j ≡ i
split-+-inl {m = suc m} {i = i} p with fin-view i
... | zero with reflᵢ ← p = refl
... | suc i' with inl j' ← split-+ {m} i' in Heq | reflᵢ ← p =
  ap fsuc (split-+-inl Heq)

split-+-inject : ∀ j → split-+ (inject (+-≤l m n) j) ≡ inl j
split-+-inject j with fin-view j
... | zero  = refl
... | suc j' = ap (⊎-map _ _) (split-+-inject j')

split-+-inr : {i : Fin (m + n)} {j : Fin n} → split-+ i ≡ᵢ inr j → fshift m j ≡ i
split-+-inr {m = zero} reflᵢ = refl
split-+-inr {m = suc m} {i = i} p with fin-view i
... | suc i' with inr j' ← split-+ {m} i' in Heq | reflᵢ ← p =
  ap fsuc (split-+-inr Heq)

split-+-fshift : ∀ m (j : Fin n) → split-+ (fshift m j) ≡ inr j
split-+-fshift zero j    = refl
split-+-fshift (suc m) j = ap (⊎-map _ _) (split-+-fshift m j)
