open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Prelude

module Lib.Cat.Concrete where

-- Our definitions of concrete categories and presheaves.

open Functor

private variable
  o ℓ κ : Level

record Conc-category κ (C : Precategory o ℓ) : Type (o ⊔ ℓ ⊔ lsuc κ) where
  no-eta-equality
  open Precategory C

  field
    underlying          : Functor C (Sets κ)
    underlying-faithful : is-faithful underlying

  ob∣_∣ : Ob → Type κ
  ob∣ c ∣ = underlying ʻ c

  hom∣_∣ : {o₁ o₂ : ⌞ C ⌟} → Hom o₁ o₂ → ob∣ o₁ ∣ → ob∣ o₂ ∣
  hom∣ f ∣ = underlying .F₁ f

  is-conc-hom : (U V : Ob) → (ob∣ U ∣ → ob∣ V ∣) → Type (ℓ ⊔ κ)
  is-conc-hom U V f = f ∈ fibre hom∣_∣

  is-conc-hom-prop : (U V : Ob) (f : ob∣ U ∣ → ob∣ V ∣) → is-prop (is-conc-hom U V f)
  is-conc-hom-prop U V f (g , p) (h , q) = underlying-faithful (p ∙ sym q) ,ₚ prop!

  hom≃conc-hom : {U V : Ob} → Hom U V ≃ ∫ₚ (is-conc-hom U V)
  hom≃conc-hom .fst = λ f → hom∣ f ∣ , f , refl
  hom≃conc-hom .snd = is-iso→is-equiv $
    iso (λ (_ , f , _) → f)
      (λ (f , g , p) → p ,ₚ refl ,ₚ prop!)
      (λ _ → refl)

module _
  {C D : Precategory o ℓ} (C-conc : Conc-category κ C) (D-conc : Conc-category κ D)
  where
  private
    module Cc = Conc-category C-conc
    module Dc = Conc-category D-conc

  is-concrete-functor : Functor C D → Type _
  is-concrete-functor F = Dc.underlying F∘ F ≅ⁿ Cc.underlying
