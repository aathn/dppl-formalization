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
open import Cat.Functor.Compose
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Properties
open import Cat.Functor.Subcategory
open import Cat.Instances.Presheaf.Limits
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Instances.Shape.Two
import Cat.Functor.Hom as Hom
import Cat.Reasoning as Cr
import Cat.Functor.Reasoning as Fr

open _=>_ hiding (op)
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
    conc-section : {U : ⌞ C ⌟} → A ʻ U → ob∣ U ∣ → A ʻ ⋆
    conc-section AU f = A ⟪ f ⟫ AU

    -- A presheaf is *concrete* if the concrete sections are a
    -- faithful representation of the functor's action.
    is-concrete : Type (o ⊔ ℓ ⊔ κ)
    is-concrete = ∀ {U} → injective (conc-section {U})

-- The concrete presheaves as a full subcategory of presheaves
ConcPSh : ∀ κ {o ℓ} {C : Precategory o ℓ} → Conc-category C → Precategory _ _
ConcPSh κ {C = C} Conc = Restrict {C = PSh κ C} (is-concrete Conc)

module _ {o ℓ} {C : Precategory o ℓ} (Conc : Conc-category C) where
  open Conc-category Conc
  open Hom C
  open Cr._≅_
  open Cr.Inverses

  private
    module C = Cr C
    module CPSh {κ} = Precategory (ConcPSh κ Conc)

  is-conc-section : ∀ {κ U} (A : CPSh.Ob {κ}) → (ob∣ U ∣ → A ʻ ⋆) → Type (ℓ ⊔ κ)
  is-conc-section {U = U} (A , _) f = Σ[ au ∈ A ʻ U ] f ≡ conc-section Conc A au

  is-conc-hom : ∀ {κ} (A B : CPSh.Ob {κ}) → (A ʻ ⋆ → B ʻ ⋆) → Type (o ⊔ ℓ ⊔ κ)
  is-conc-hom A B f =
    ∀ {U} (g : ob∣ U ∣ → A ʻ ⋆) → is-conc-section A g → is-conc-section B (f ⊙ g)

  -- Morphisms of concrete presheaves are given by functions of underlying sets
  -- which preserve membership in is-conc-section.
  record Conc-hom {κ} (A B : CPSh.Ob {κ}) : Type (o ⊔ ℓ ⊔ κ) where
    constructor conc-hom
    field
      to     : A ʻ ⋆ → B ʻ ⋆
      is-hom : is-conc-hom A B to

  open Conc-hom

  is-conc-hom-prop
    : ∀ {κ} (A B : CPSh.Ob {κ}) (f : A ʻ ⋆ → B ʻ ⋆) → is-prop (is-conc-hom A B f)
  is-conc-hom-prop A (B , Bconc) f x y = ext λ g au p →
    let _ , Hx = x g (au , p)
        _ , Hy = y g (au , p)
    in
    (Bconc (sym Hx ∙ Hy)) ,ₚ prop!

  Conc-hom-path
    : ∀ {κ} {A B : CPSh.Ob {κ}} {f g : Conc-hom A B} → f .to ≡ g .to → f ≡ g
  Conc-hom-path p i .to                         = p i
  Conc-hom-path {A = A} {B} {f} {g} p i .is-hom =
    is-prop→pathp (λ i → is-conc-hom-prop A B (p i)) (f .is-hom) (g .is-hom) i

  instance
    Extensional-conc-hom
      : ∀ {ℓr κ} {A B : CPSh.Ob {κ}} ⦃ sa : Extensional (A ʻ ⋆ → B ʻ ⋆) ℓr ⦄
      → Extensional (Conc-hom A B) _
    Extensional-conc-hom ⦃ sa ⦄ = injection→extensional! Conc-hom-path sa

    Funlike-conc-hom
      : ∀ {κ} {A B : CPSh.Ob {κ}} → Funlike (Conc-hom A B) (A ʻ ⋆) (λ _ → B ʻ ⋆)
    Funlike-conc-hom = record { _·_ = λ f x → apply (f .to) x }

    H-Level-Conc-hom : ∀ {κ} {A B : CPSh.Ob {κ}} {n} → H-Level (Conc-hom A B) (2 + n)
    H-Level-Conc-hom {A = A} {B} = basic-instance 2 $ Iso→is-hlevel 2 eqv $
      Σ-is-hlevel 2 (hlevel 2) λ x →
      is-hlevel-suc 1 (is-conc-hom-prop A B x)
      where unquoteDecl eqv = declare-record-iso eqv (quote Conc-hom)

  Conc-hom→Hom : ∀ {κ} {A B : CPSh.Ob {κ}} → Conc-hom A B → CPSh.Hom A B
  Conc-hom→Hom {A = A , Aconc} {B , Bconc} (conc-hom f Hf) = full-hom λ where
    .η U au           → Hf (conc-section Conc A au) (au , refl) .fst
    .is-natural _ _ g → ext λ au →
      let bu , p   = Hf (conc-section Conc A au) (au , refl)
          bu' , p' = Hf (conc-section Conc A (A ⟪ g ⟫ au)) (_ , refl)
      in
      Bconc $ ext λ h →
        B ⟪ h ⟫ bu'          ≡˘⟨ ap f (A .F-∘ _ _ $ₚ au) ∙ p' $ₚ _ ⟩
        f (A ⟪ g C.∘ h ⟫ au) ≡⟨ p $ₚ _ ∙ B .F-∘ _ _ $ₚ bu ⟩
        B ⟪ h ⟫ (B ⟪ g ⟫ bu) ∎

  Hom→Conc-hom : ∀ {κ} {A B : CPSh.Ob {κ}} → CPSh.Hom A B → Conc-hom A B
  Hom→Conc-hom {A = A , AConc} {B , Bconc} f =
    conc-hom (f .hom .η ⋆) λ {U} g (au , p) →
    f .hom .η U au ,
    (f .hom .η ⋆ ⊙ g                      ≡⟨ ap (f .hom .η ⋆ ⊙_) p ⟩
     f .hom .η ⋆ ⊙ conc-section Conc A au ≡⟨ ext (λ x → f .hom .is-natural _ _ x $ₚ au) ⟩
     conc-section Conc B (f .hom .η U au) ∎)

  Conc-hom≃Hom : ∀ {κ} {A B : CPSh.Ob {κ}} → Conc-hom A B ≃ CPSh.Hom A B
  Conc-hom≃Hom {A = A , Aconc} {B , Bconc} = Iso→Equiv $ Conc-hom→Hom ,
    iso Hom→Conc-hom
      (λ f → ext λ _ _ → refl)
      (λ f → ext λ x →
        let y , p = f .is-hom (conc-section Conc A x) (_ , refl) in
        y                  ≡˘⟨ B .F-id $ₚ y ⟩
        B ⟪ C.id ⟫ y       ≡˘⟨ p $ₚ C.id ⟩
        f · (A ⟪ C.id ⟫ x) ≡⟨ ap (f ·_) (A .F-id $ₚ x) ⟩
        f · x              ∎)

  -- Representable presheaves are concrete
  Conc-よ₀ : (U : ⌞ C ⌟) → CPSh.Ob
  Conc-よ₀ U = よ₀ U , ⋆-hom-faithful

  module _ {o' ℓ'} {D : Precategory o' ℓ'} (ConcD : Conc-category D) where
    private module CD = Conc-category ConcD

    conc-dir-image
      : ∀ {κ} (F : Functor D C)
      → (F .F₀ CD.⋆ C.≅ ⋆) → (∀ {U} → is-surjective (F .F₁ {CD.⋆} {U}))
      → Functor (ConcPSh κ Conc) (ConcPSh κ ConcD)
    conc-dir-image {κ} F α F-onto-points =
      sub-functor (G F∘ Forget-subcat) λ (A , conc) → G-concrete A conc
      where
        G : Functor (PSh κ C) (PSh κ D)
        G = precompose (op F)

        G-concrete : ∀ A → is-concrete Conc A → is-concrete ConcD (G .F₀ A)
        G-concrete A conc {U} {x} {y} H≡ = conc $ funext λ f →
          let module A = Fr A in
          case F-onto-points (f C.∘ α .to) of λ g p →
            A ⟪ f ⟫ x                           ≡⟨ A.expand (C.insertr (α .inverses .invl)) $ₚ x ⟩
            A ⟪ α .from ⟫ (A ⟪ f C.∘ α .to ⟫ x) ≡⟨ ap (A ⟪ _ ⟫_) (sym A.⟨ p ⟩ $ₚ x ∙ H≡ $ₚ g ∙ A.⟨ p ⟩ $ₚ y) ⟩
            A ⟪ α .from ⟫ (A ⟪ f C.∘ α .to ⟫ y) ≡⟨ A.collapse (C.cancelr (α .inverses .invl)) $ₚ y ⟩
            A ⟪ f ⟫ y                           ∎

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

