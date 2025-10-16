module Lib.Cat.Concrete where

-- Our definitions of concrete categories and presheaves.

open import Lib.Cat.Sheafification
open import Lib.Cat.Subcategory

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Exponential
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Product
open import Cat.Diagram.Product
open import Cat.Diagram.Terminal
open import Cat.Functor.Base
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Properties
open import Cat.Functor.Subcategory
open import Cat.Instances.Presheaf.Limits
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Instances.Shape.Two
import Cat.Functor.Hom as Hom

open _=>_
open Functor
open Subcat-hom

record Conc-category {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Precategory C
  open Hom C

  field
    terminal : Terminal C

  open Terminal terminal public renaming (top to ⋆ ; has⊤ to ⋆-is-terminal)

  field
    ⋆-hom-faithful : is-faithful Hom[ ⋆ ,-]

  ob∣_∣ : Ob → Type ℓ
  ob∣ c ∣ = Hom[ ⋆ ,-] ʻ c

  hom∣_∣ : {o₁ o₂ : ⌞ C ⌟} → Hom o₁ o₂ → ob∣ o₁ ∣ → ob∣ o₂ ∣
  hom∣_∣ = Hom[ ⋆ ,-] .F₁

module _ {o ℓ} {C : Precategory o ℓ} (Conc : Conc-category C) where
  open Conc-category Conc
  open Hom C

  module _ {κ} (A : Functor (C ^op) (Sets κ)) where
    -- We take the concrete sections of A at U to be the maps
    -- g : ob∣ U ∣ → A ʻ ⋆
    -- given by the contravariant action of A on a point
    -- h : ob∣ U ∣ = Hom ⋆ U.
    conc-sections : (U : ⌞ C ⌟) → A ʻ U → ob∣ U ∣ → A ʻ ⋆
    conc-sections U AU f = A ⟪ f ⟫ AU

    -- A presheaf is *concrete* if the concrete sections are a
    -- faithful representation of the functor's action.
    is-concrete : Type (o ⊔ ℓ ⊔ κ)
    is-concrete = ∀ {U} → injective (conc-sections U)

-- The concrete presheaves as a full subcategory of presheaves
ConcPSh : ∀ κ {o ℓ} {C : Precategory o ℓ} → Conc-category C → Precategory _ _
ConcPSh κ {C = C} Conc = Restrict {C = PSh κ C} (is-concrete Conc)

module _ {o ℓ} {C : Precategory o ℓ} (Conc : Conc-category C) where
  open Conc-category Conc
  open Hom C

  -- Representable presheaves are concrete
  Conc-よ₀ : (U : ⌞ C ⌟) → ⌞ ConcPSh ℓ Conc ⌟
  Conc-よ₀ U = よ₀ U , ⋆-hom-faithful

  よ⋆-is-terminal : is-terminal (ConcPSh ℓ Conc) (Conc-よ₀ ⋆)
  よ⋆-is-terminal X .centre = full-hom record
    { η = λ _ _ → ! ; is-natural = λ _ _ _ → ext λ _ → !-unique₂ _ _ }
  よ⋆-is-terminal X .paths f = ext λ _ _ → !-unique _

  -- Limits of concrete presheaves can be computed pointwise.
  is-concrete-limit
    : ∀ {o' ℓ'} {D : Precategory o' ℓ'} {F : Functor D (PSh ℓ C)} {L} {ψ}
    → is-limit F L ψ
    → ((d : ⌞ D ⌟) → is-concrete Conc (F · d))
    → is-concrete Conc L
  is-concrete-limit {F = F} {L} {ψ} lim dconc {U} {x} {y} p =
    -- Mimicking Yoneda voodoo from Cat.Instances.Sheaf.Limits
    unyo-path $ lim.unique₂ {x = よ₀ U} _
      (λ f → yo-natl (sym (ψ .is-natural _ _ _ ηₚ _ $ₚ _))) (λ j → yo-natl refl)
      (λ j → yo-natl (dconc j $ funext λ g →
        F.₁ j g (ψ .η j .η U y) ≡˘⟨ ψ .η j .is-natural _ _ _ $ₚ _ ⟩
        ψ .η j .η _ (L.₁ g y)   ≡˘⟨ ap (ψ .η j .η _) (p $ₚ g) ⟩
        ψ .η j .η _ (L.₁ g x)   ≡⟨ ψ .η j .is-natural _ _ _ $ₚ _ ⟩
        F.₁ j g (ψ .η j .η U x) ∎))
    where
    module lim = is-limit lim
    module F x = Functor (F .F₀ x)
    module L = Functor L

  open Cartesian-category
  open is-product
  open Product
  open Terminal

  ConcPSh-terminal : Terminal (ConcPSh ℓ Conc)
  ConcPSh-terminal .top .fst = ⊤PSh ℓ C
  ConcPSh-terminal .top .snd _ = refl
  ConcPSh-terminal .has⊤ (A , _) = record
    { centre = full-hom (PSh-terminal _ C .has⊤ A .centre)
    ; paths  = λ f → Subcat-hom-path
      $ PSh-terminal _ C .has⊤ A .paths (f .hom)
    }

  ConcPSh-products : has-products (ConcPSh ℓ Conc)
  ConcPSh-products (A , aconc) (B , bconc) = prod where
    prod' = PSh-products _ C A B

    prod : Product (ConcPSh ℓ Conc) _ _
    prod .apex .fst = prod' .apex
    prod .apex .snd = is-concrete-limit
      {F = 2-object-diagram _ _} {ψ = 2-object-nat-trans _ _}
      (is-product→is-limit (PSh _ C) (prod' .has-is-product))
      λ { true → aconc ; false → bconc }
    prod .π₁ = full-hom (prod' .π₁)
    prod .π₂ = full-hom (prod' .π₂)
    prod .has-is-product .⟨_,_⟩ f g =
      full-hom (prod' .⟨_,_⟩ (f .hom) (g .hom))
    prod .has-is-product .π₁∘⟨⟩ = Subcat-hom-path $ prod' .π₁∘⟨⟩
    prod .has-is-product .π₂∘⟨⟩ = Subcat-hom-path $ prod' .π₂∘⟨⟩
    prod .has-is-product .unique p q = Subcat-hom-path
      $ prod' .unique (ap hom p) (ap hom q)

  ConcPSh-cartesian : Cartesian-category (ConcPSh ℓ Conc)
  ConcPSh-cartesian .terminal = ConcPSh-terminal
  ConcPSh-cartesian .products = ConcPSh-products


module _ {ℓ} {C : Precategory ℓ ℓ} (Conc : Conc-category C) where
  open Cartesian-closed
  open Exponential
  open is-exponential

  -- Concrete presheaves form an exponential ideal, just like sheaves.
  -- Morally, this is because if we can distinguish points of B, then we
  -- can also distinguish maps into B.
  is-concrete-exponential
    : (A B : Functor (C ^op) (Sets ℓ))
    → is-concrete Conc B
    → is-concrete Conc (PSh[_,_] C A B)
  is-concrete-exponential A B bconc {x = x} {y} p =
    ext λ V f au → bconc $ ext λ g →
      B ⟪ g ⟫ x .η V (f , au)            ≡˘⟨ x .is-natural V _ g $ₚ (f , au) ⟩
      _                                  ≡˘⟨ ap (λ fg → x .η _ (fg , _)) (idr _) ⟩
      x .η _ ((f ∘ g) ∘ id , A ⟪ g ⟫ au) ≡⟨ (p $ₚ (f ∘ g) ηₚ _) $ₚ (id , A ⟪ g ⟫ au) ⟩
      y .η _ ((f ∘ g) ∘ id , A ⟪ g ⟫ au) ≡⟨ ap (λ fg → y .η _ (fg , _)) (idr _) ⟩
      _                                  ≡⟨ y .is-natural V _ g $ₚ (f , au) ⟩
      B ⟪ g ⟫ y .η V (f , au)            ∎
    where open Precategory C

  ConcPSh-closed : Cartesian-closed (ConcPSh ℓ Conc) (ConcPSh-cartesian Conc)
  ConcPSh-closed .has-exp (A , _) (B , bconc) = exp where
    exp' = PSh-closed C .has-exp A B

    exp : Exponential (ConcPSh ℓ Conc) _ _ _
    exp .B^A .fst = exp' .B^A
    exp .B^A .snd = is-concrete-exponential A B bconc
    exp .ev = full-hom (exp' .ev)
    exp .has-is-exp .ƛ f = full-hom (exp' .ƛ (f .hom))
    exp .has-is-exp .commutes m = Subcat-hom-path
      $ exp' .commutes (m .hom)
    exp .has-is-exp .unique m p = Subcat-hom-path
      $ exp' .unique (m .hom) (ap hom p)

