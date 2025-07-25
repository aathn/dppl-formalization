module Lib.Cat.Concrete where

-- Our definitions of concrete categories, sites, and sheaves.

open import Cat.Prelude
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Properties
open import Cat.Site.Base
import Cat.Functor.Hom as Hom

open import Data.Image

record Conc-category {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Precategory C
  open Hom C

  -- We use a more restrictive definition of concrete category than
  -- the standard presentation in that we require the forgetful
  -- functor to be representable by a terminal object (following
  -- Matache et al.).

  field
    terminal : Terminal C

  open Terminal terminal public renaming (top to ⋆ ; has⊤ to ⋆-is-terminal)

  field
    ⋆-hom-faithful : is-faithful Hom[ ⋆ ,-]

  open Functor

  ob∣_∣ : Ob → Type ℓ
  ob∣ c ∣ = Hom[ ⋆ ,-] ʻ c

  hom∣_∣ : {o₁ o₂ : ⌞ C ⌟} → Hom o₁ o₂ → ob∣ o₁ ∣ → ob∣ o₂ ∣
  hom∣_∣ = Hom[ ⋆ ,-] .F₁

module _ {o ℓ} {C : Precategory o ℓ} (Conc : Conc-category C) where

  record Conc-coverage {ℓc} (J : Coverage C ℓc) : Type (o ⊔ ℓ ⊔ ℓc) where
    no-eta-equality
    open Precategory C
    open Conc-category Conc
    open Coverage J

    field
      is-concrete :
        ∀ {U} {S : J ʻ U} (x : ob∣ U ∣)
        → ------------------------------------------
        ∃[ V ∈ C ] Σ[ f ∈ Hom V U ] Σ[ a ∈ ob∣ V ∣ ]
        f ∈ S × hom∣ f ∣ a ≡ x

module _ {o ℓ ℓc ℓs}
  {C : Precategory o ℓ}
  {Conc : Conc-category C}
  {J : Coverage C ℓc}
  (Conc-J : Conc-coverage Conc J)
  where
  open Conc-category Conc
  open Functor

  module _ (A : Functor (C ^op) (Sets ℓs)) where
    -- We take the "concrete sections" of A at U to be the maps
    -- g : ob∣ U ∣ → A ʻ ⋆
    -- given by the contravariant action of A on a morphism
    -- h : ob∣ U ∣ = Hom ⋆ U.
    -- In other words, given h which intuitively represents a constant
    -- map into U, we obtain a point in A ʻ ⋆ by restricting along h.
    conc-sections : (U : ⌞ C ⌟) → A ʻ U → ob∣ U ∣ → A ʻ ⋆
    conc-sections U AU f = A ⟪ f ⟫ AU

    -- And a presheaf is concrete if the concrete sections are a
    -- faithful representation of the functor's action.
    is-conc-presheaf : Type (o ⊔ ℓ ⊔ ℓs)
    is-conc-presheaf = ∀ {U} → injective (conc-sections U)

    is-conc-sheaf : Type _
    is-conc-sheaf = is-conc-presheaf × is-sheaf J A

    -- Interestingly, the concrete sections can be used to define a
    -- concretized version of any presheaf.
    private
      conc-sections-is-set : ∀ {U} → is-set (ob∣ U ∣ → A ʻ ⋆)
      conc-sections-is-set = fun-is-hlevel 2 (A .F₀ ⋆ .is-tr)

      abstract
        conc-sections-locally-small : ∀ {U} → is-identity-system {A = ob∣ U ∣ → A ʻ ⋆} (λ x y → □ (x ≡ y)) (λ x → inc refl)
        conc-sections-locally-small = is-set→locally-small conc-sections-is-set

      module Im {U : ⌞ C ⌟} = Replacement (conc-sections-locally-small {U})

    concretize-presheaf : Functor (C ^op) (Sets ℓs)
    ∣ concretize-presheaf .F₀ U ∣ = Im.Image (conc-sections U)
    concretize-presheaf .F₀ U .is-tr =
      Im.Image-is-hlevel (conc-sections U) 1 conc-sections-is-set
    concretize-presheaf .F₁ {x = U} {y = V} f (Im.inc x) = Im.inc (A ⟪ f ⟫ x)
    concretize-presheaf .F₁ {x = U} {y = V} f (Im.quot p i) = {!!}
      -- Im.inc (conc-sections (f)
      -- let foo = Im.quot
    concretize-presheaf .F-id = {!!}
    concretize-presheaf .F-∘ = {!!}


  ConcSheaves : Precategory (o ⊔ ℓ ⊔ ℓc ⊔ lsuc ℓs) (o ⊔ ℓ ⊔ ℓs)
  ConcSheaves = Restrict {C = Sheaves J ℓs} (is-conc-presheaf ⊙ fst)

  -- The evident forgetful functor from ConcSheaves to Sheaves
  forget-conc : Functor ConcSheaves (Sheaves J ℓs)
  forget-conc .F₀ = fst
  forget-conc .F₁ x = x
  forget-conc .F-id = refl
  forget-conc .F-∘ f g = refl

  make-free-conc : ∀ F → Free-object forget-conc F
  make-free-conc = {!!}

