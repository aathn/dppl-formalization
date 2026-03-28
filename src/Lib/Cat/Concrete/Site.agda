open import Cat.Site.Constructions
open import Cat.Instances.Slice
open import Cat.Diagram.Sieve
open import Lib.Cat.Concrete
open import Cat.Site.Base
open import Cat.Prelude

module Lib.Cat.Concrete.Site where

private variable
  o ℓ κ : Level

module _ {C : Precategory o ℓ} (C-conc : Conc-category κ C) where
  open Conc-category C-conc
  open /-Obj

  is-jointly-surjective : ∀ {U} → Sieve C U → Type _
  is-jointly-surjective {U} fs =
    ∀ (x : ob∣ U ∣) → ∃[ f ∈ Slice C U ] f ∈ fs × x ∈ fibre hom∣ f .map ∣

  point-coverage : Coverage C _
  point-coverage = from-stable-property is-jointly-surjective
    λ f s surj x → {!!}
      -- case surj (hom∣ f ∣ x) of λ
      --   (cut g) Hg y p → inc (cut {!!} , {!!})
  -- point-topology .covering U fs =
  --   ∀ (x : ob∣ U ∣) → ∃[ f ∈ Slice C U ] f ∈ fs × x ∈ fibre hom∣ f .map ∣
  -- point-topology .has-is-prop = hlevel 1
  -- point-topology .stable  = {!!}
  -- point-topology .maximal = {!!}
  -- point-topology .local   = {!!}
