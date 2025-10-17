module Lib.Data.List where

open import 1Lab.Prelude
open import Data.List.Base

module ListSyntax where
  open import Data.List.Base public using ([] ; _∷_)

map-comp
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (xs : List A) (f : B → C) (g : A → B)
  → map f (map g xs) ≡ map (f ∘ g) xs
map-comp [] f g = refl
map-comp (x ∷ xs) f g = ap (f (g x) ∷_) (map-comp xs f g)
