module Lib.Cat.Sheafification where

open import Cat.Prelude
open import Cat.Site.Base
open import Cat.Site.Sheafification

module _ {o ℓ ℓc ℓs} {C : Precategory o ℓ} {J : Coverage C ℓc} {A : Functor (C ^op) (Sets ℓs)} where
  open Sheafification J A

  inc-inj : {U : ⌞ C ⌟} {x y : A ʻ U} → is-separated J A → Sheafification.inc x ≡ inc y → x ≡ y
  inc-inj {x = x} {y} Hsep p = Hsep {!!} λ f Hf →
    {!!}
    -- ap f p where
    -- f : {U : ⌞ C ⌟} → Sheafify₀ ʻ U → A ʻ U
    -- f (inc x) = x
    -- f (map g x) = A ⟪ g ⟫ (f x)
    -- f (glue _ _ _) = {!!}
    -- f (map-id x i) = {!!}
    -- f (map-∘ x i) = {!!}
    -- f (inc-natural x i) = {!!}
    -- f (sep c l i) = {!!}
    -- f (glues c p g f₁ hf i) = {!!}
    -- f (squash x x₁ x₂ y i i₁) = {!!}
