module Lib.Cat.Concrete where

-- Our definitions of concrete categories, sites, and sheaves.

open import Cat.Prelude
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Properties
open import Cat.Site.Base
import Cat.Functor.Hom as Hom

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

module _ {o ℓ ℓc}
  {C : Precategory o ℓ}
  {Conc : Conc-category C}
  {J : Coverage C ℓc}
  (Conc-J : Conc-coverage Conc J)
  where

  open Precategory C
  open Conc-category Conc
  open Functor

  private variable
    ℓs : Level

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

  -- The category of concrete sheaves is given as a subcategory of
  -- sheaves.
  ConcSheaves : Precategory (o ⊔ ℓ ⊔ ℓc ⊔ lsuc ℓs) (o ⊔ ℓ ⊔ ℓs)
  ConcSheaves {ℓs} = Restrict {C = Sheaves J ℓs} (is-conc-presheaf ⊙ fst)

  module _ (A : Functor (C ^op) (Sets ℓs)) where
    -- Interestingly, the concrete sections can be used to define a
    -- concretized version of any presheaf.
    -- Due to reasons explained in Data.Image, the resulting universe
    -- level is potentially raised by this construction.  This could
    -- be resolved using the Image type of that module, but for now
    -- this works for us.
    concretize-presheaf : Functor (C ^op) (Sets (ℓ ⊔ ℓs))
    concretize-presheaf .F₀ U = el (image (conc-sections A U)) (hlevel 2)
    concretize-presheaf .F₁ f (fr , ∥r∥) =
      fr ⊙ hom∣ f ∣ ,
      ∥-∥-rec (hlevel 1)
        (λ (r , Hr) → inc (A ⟪ f ⟫ r , funext λ g → happly (sym (F-∘ A g f)) r ∙ happly Hr (f ∘ g)))
        ∥r∥
    concretize-presheaf .F-id =
      funext λ (fr , ∥r∥) → Σ-pathp.to
        (ap (fr ⊙_) (funext idl) , is-prop→pathp (λ i → hlevel 1) _ _)
    concretize-presheaf .F-∘ f g =
      funext λ (fr , ∥r∥) → Σ-pathp.to
        (ap (fr ⊙_) (funext (sym ⊙ assoc g f)) , is-prop→pathp (λ i → hlevel 1) _ _)

    -- We check that this indeed gives a concrete presheaf.
    concretize-is-concrete : is-conc-presheaf concretize-presheaf
    concretize-is-concrete {x = x} {y} p = {!!}

    -- This also works at the level of sheaves.
    concretize-is-separated : is-separated J A → is-separated J concretize-presheaf
    concretize-is-separated sep S {x , _} {y , _} p-eq = Σ-pathp.to
      ( funext (λ g → {!!})
      , is-prop→pathp (λ i → hlevel 1) _ _
      )

    concretize-is-sheaf : is-sheaf J A → is-sheaf J concretize-presheaf
    concretize-is-sheaf shf .whole S p = {!!}
    concretize-is-sheaf shf .glues S p = {!!}
    concretize-is-sheaf shf .separate = concretize-is-separated (shf .separate)

  -- The evident forgetful functor from ConcSheaves to Sheaves
  forget-conc : Functor ConcSheaves (Sheaves J ℓs)
  forget-conc .F₀ = fst
  forget-conc .F₁ x = x
  forget-conc .F-id = refl
  forget-conc .F-∘ f g = refl

  make-free-conc : ∀ F → Free-object (forget-conc {ℓs}) F
  make-free-conc = {!!}
