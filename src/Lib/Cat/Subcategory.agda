open import Cat.Prelude

module Lib.Cat.Subcategory {o h} {C : Precategory o h} where

open import Cat.Functor.Subcategory
import Cat.Reasoning as CR

private
  module C = CR C
  variable ℓ : Level

module _ {o' h'} {S : Subcat C o' h'} where
  open Subcat-hom

  Subcat-hom-path : {x y : ∫ₚ S} {f g : Subcat-hom S x y} → f .hom ≡ g .hom → f ≡ g
  Subcat-hom-path = Subcat-hom-pathp refl refl

-- We give an alternative definition of full subcategories
-- (c.f. Cat.Functor.FullSubcategory and Cat.Functor.Subcategory), which wraps
-- morphisms in a record type to improve type inference.

Full-subcat : (P : C.Ob → Type ℓ) → Subcat C ℓ lzero
Full-subcat P .Subcat.is-ob             = P
Full-subcat P .Subcat.is-hom      _ _ _ = ⊤
Full-subcat P .Subcat.is-hom-prop _ _ _ = hlevel 1
Full-subcat P .Subcat.is-hom-id   _     = tt
Full-subcat P .Subcat.is-hom-∘    _ _   = tt

Full-hom : (P : C.Ob → Type ℓ) → Σ C.Ob P → Σ C.Ob P → Type h
Full-hom P = Subcat-hom (Full-subcat P)

pattern full-hom f = sub-hom f tt

Full-hom≃Hom
  : {P : C.Ob → Type ℓ} {x y : Σ C.Ob P}
  → Full-hom P x y ≃ C.Hom (x .fst) (y .fst)
Full-hom≃Hom .fst = Subcat-hom.hom
Full-hom≃Hom .snd = is-iso→is-equiv
  $ iso full-hom (λ _ → refl) (λ _ → Subcat-hom-path refl)

Restrict : (P : C.Ob → Type ℓ) → Precategory (o ⊔ ℓ) h
Restrict P = Subcategory (Full-subcat P)

module _ {P : C.Ob → Type ℓ} where
  private
    Sub : Precategory (o ⊔ ℓ) h
    Sub = Restrict P
    module Sub = CR Sub

  open Functor
  open _=>_
  open Subcat-hom

  sub-functor
    : ∀ {o' h'} {D : Precategory o' h'} (F : Functor D C)
    → (∀ d → P (F .F₀ d)) → Functor D Sub
  sub-functor F HP .F₀ d    = F .F₀ d , HP d
  sub-functor F HP .F₁ f    = full-hom (F .F₁ f)
  sub-functor F HP .F-id    = Subcat-hom-path (F .F-id)
  sub-functor F HP .F-∘ f g = Subcat-hom-path (F .F-∘ f g)

  sub-nat
    : ∀ {o' h'} {D : Precategory o' h'} {F G : Functor D Sub}
    → Forget-subcat F∘ F => Forget-subcat F∘ G → F => G
  sub-nat α .η x              = full-hom (α .η x)
  sub-nat α .is-natural _ _ f = Subcat-hom-path (α .is-natural _ _ f)

  iso→sub-iso : {x y : Σ C.Ob P} → x .fst C.≅ y .fst → x Sub.≅ y
  iso→sub-iso f = Sub.make-iso (full-hom (C.to f)) (full-hom (C.from f))
    (Subcat-hom-path (C.invl f)) (Subcat-hom-path (C.invr f))
