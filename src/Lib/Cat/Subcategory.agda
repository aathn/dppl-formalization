open import Cat.Prelude

module Lib.Cat.Subcategory {o h} {C : Precategory o h} where

open import Cat.Functor.Subcategory

private
  module C = Precategory C
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
