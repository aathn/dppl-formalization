module Lib.Cat.Concrete where

-- Our definitions of concrete categories and presheaves.

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Exponential
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Product
open import Cat.Diagram.Product
open import Cat.Diagram.Product.Finite
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Terminal
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Properties
open import Cat.Functor.FullSubcategory
open import Cat.Monoidal.Base
open import Cat.Monoidal.Instances.Cartesian
open import Cat.Instances.Presheaf.Limits
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Instances.Shape.Two
open import Data.Fin.Base
open import Data.Fin.Properties
import Cat.Functor.Hom as Hom
import Cat.Reasoning as Cr
import Cat.Functor.Reasoning as Fr

open _=>_ hiding (op)
open Functor

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

  is-conc-hom : (U V : Ob) → (ob∣ U ∣ → ob∣ V ∣) → Type ℓ
  is-conc-hom U V f = Σ[ g ∈ Hom U V ] f ≡ hom∣ g ∣

  is-conc-hom-prop : (U V : Ob) (f : ob∣ U ∣ → ob∣ V ∣) → is-prop (is-conc-hom U V f)
  is-conc-hom-prop U V f (g , p) (h , q) = ⋆-hom-faithful (sym p ∙ q) ,ₚ prop!

  hom≃conc-hom : {U V : Ob} → Hom U V ≃ ∫ₚ (is-conc-hom U V)
  hom≃conc-hom .fst = λ f → hom∣ f ∣ , f , refl
  hom≃conc-hom .snd = is-iso→is-equiv $
    iso (λ (_ , f , _) → f)
      (λ (f , g , p) → sym p ,ₚ refl ,ₚ prop!)
      (λ _ → refl)

module _ {o ℓ} {C : Precategory o ℓ} (Conc : Conc-category C) where
  open Conc-category Conc

  module _ {κ} (A : Functor (C ^op) (Sets κ)) where
    -- The concrete sections of A at U are the maps
    -- g : ob∣ U ∣ → A ʻ ⋆
    -- given by the contravariant action of A on a point
    -- h : ob∣ U ∣ = Hom ⋆ U.
    conc-section : {U : ⌞ C ⌟} → A ʻ U → ob∣ U ∣ → A ʻ ⋆
    conc-section au f = A ⟪ f ⟫ au

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

  is-conc-section : ∀ {κ} (A : CPSh.Ob {κ}) {U} → (ob∣ U ∣ → A ʻ ⋆) → Type (ℓ ⊔ κ)
  is-conc-section (A , _) {U} f = Σ[ au ∈ A ʻ U ] f ≡ conc-section Conc A au

  is-conc-section-prop
    : ∀ {κ} (A : CPSh.Ob {κ}) {U} (f : ob∣ U ∣ → A ʻ ⋆) → is-prop (is-conc-section A f)
  is-conc-section-prop (A , Aconc) f (au , p) (au' , q) = Aconc (sym p ∙ q) ,ₚ prop!

  section≃conc-section
    : ∀ {κ} (A : CPSh.Ob {κ}) {U} → A ʻ U ≃ ∫ₚ (is-conc-section A {U})
  section≃conc-section (A , _) .fst = λ au → conc-section Conc A au , _ , refl
  section≃conc-section (A , _) .snd = is-iso→is-equiv $
    iso (λ (_ , au , _) → au)
      (λ (f , au , p) → sym p ,ₚ refl ,ₚ prop!)
      (λ _ → refl)

  -- Morphisms of concrete presheaves are given by functions of underlying sets
  -- which preserve membership in is-conc-section.
  is-cpsh-hom : ∀ {κ} (A B : CPSh.Ob {κ}) → (A ʻ ⋆ → B ʻ ⋆) → Type (o ⊔ ℓ ⊔ κ)
  is-cpsh-hom A B f =
    ∀ {U : C.Ob} (au : A ʻ U) → is-conc-section B (f ⊙ conc-section Conc (A .fst) au)

  record Cpsh-hom {κ} (A B : CPSh.Ob {κ}) : Type (o ⊔ ℓ ⊔ κ) where
    no-eta-equality
    constructor conc-hom
    field
      to     : A ʻ ⋆ → B ʻ ⋆
      is-hom : is-cpsh-hom A B to

  open Cpsh-hom

  is-cpsh-hom-prop
    : ∀ {κ} (A B : CPSh.Ob {κ}) (f : A ʻ ⋆ → B ʻ ⋆) → is-prop (is-cpsh-hom A B f)
  is-cpsh-hom-prop A B f x y = ext λ au → is-conc-section-prop B (f ⊙ _) _ _

  Cpsh-hom-path
    : ∀ {κ} {A B : CPSh.Ob {κ}} {f g : Cpsh-hom A B} → f .to ≡ g .to → f ≡ g
  Cpsh-hom-path p i .to                         = p i
  Cpsh-hom-path {A = A} {B} {f} {g} p i .is-hom =
    is-prop→pathp (λ i → is-cpsh-hom-prop A B (p i)) (f .is-hom) (g .is-hom) i

  unquoteDecl Cpsh-hom-record-iso =
    declare-record-iso Cpsh-hom-record-iso (quote Cpsh-hom)

  instance
    Extensional-conc-hom
      : ∀ {ℓr κ} {A B : CPSh.Ob {κ}} ⦃ sa : Extensional (A ʻ ⋆ → B ʻ ⋆) ℓr ⦄
      → Extensional (Cpsh-hom A B) _
    Extensional-conc-hom ⦃ sa ⦄ = injection→extensional! Cpsh-hom-path sa

    Funlike-conc-hom
      : ∀ {κ} {A B : CPSh.Ob {κ}} → Funlike (Cpsh-hom A B) (A ʻ ⋆) (λ _ → B ʻ ⋆)
    Funlike-conc-hom = record { _·_ = λ f x → apply (f .to) x }

    H-Level-Cpsh-hom : ∀ {κ} {A B : CPSh.Ob {κ}} {n} → H-Level (Cpsh-hom A B) (2 + n)
    H-Level-Cpsh-hom {A = A} {B} = basic-instance 2
      $ Iso→is-hlevel 2 Cpsh-hom-record-iso
      $ Σ-is-hlevel 2 (hlevel 2) λ x →
      is-hlevel-suc 1 (is-cpsh-hom-prop A B x)

  Hom→Cpsh-hom : ∀ {κ} {A B : CPSh.Ob {κ}} → CPSh.Hom A B → Cpsh-hom A B
  Hom→Cpsh-hom {A = A , _} {B , _} f =
    conc-hom (f .η ⋆) λ {U} au → f .η U au , ext (λ x → f .is-natural _ _ x $ₚ au)

  Cpsh-hom→Hom : ∀ {κ} {A B : CPSh.Ob {κ}} → Cpsh-hom A B → CPSh.Hom A B
  Cpsh-hom→Hom {A = A , _} {B , Bconc} f = λ where
    .η U au           → f .is-hom au .fst
    .is-natural _ _ g → ext λ au →
      let bu , p   = f .is-hom au
          bu' , p' = f .is-hom (A ⟪ g ⟫ au)
      in
      Bconc $ ext λ h →
        B ⟪ h ⟫ bu'              ≡˘⟨ ap (f .to) (A .F-∘ _ _ $ₚ au) ∙ p' $ₚ _ ⟩
        f .to (A ⟪ g C.∘ h ⟫ au) ≡⟨ p $ₚ _ ∙ B .F-∘ _ _ $ₚ bu ⟩
        B ⟪ h ⟫ (B ⟪ g ⟫ bu)     ∎

  Hom≃Cpsh-hom : ∀ {κ} {A B : CPSh.Ob {κ}} → CPSh.Hom A B ≃ Cpsh-hom A B
  Hom≃Cpsh-hom .fst                     = Hom→Cpsh-hom
  Hom≃Cpsh-hom {A = A , _} {B , _} .snd = is-iso→is-equiv $ iso Cpsh-hom→Hom
    (λ f → ext λ x →
      let y , p = f .is-hom x in
      y                  ≡˘⟨ B .F-id $ₚ y ⟩
      B ⟪ C.id ⟫ y       ≡˘⟨ p $ₚ C.id ⟩
      f · (A ⟪ C.id ⟫ x) ≡⟨ ap (f ·_) (A .F-id $ₚ x) ⟩
      f · x              ∎)
    (λ f → ext λ _ _ → refl)

  is-cpsh-hom'
    : ∀ {κ ℓ'} {O : C.Ob → Type κ} {A B : Type κ}
    → (P : ∀ U → (O U → A) → Type ℓ') (Q : ∀ U → (O U → B) → Type ℓ')
    → (A → B) → Type (o ⊔ ℓ' ⊔ κ)
  is-cpsh-hom' {O = O} {A} {B} P Q f =
    ∀ {U : C.Ob} (g : O U → A) → P U g → Q U (f ⊙ g)

  Cpsh-hom≃Cpsh-hom'
    : ∀ {κ ℓ'} {O : C.Ob → Type κ} {A' B' : Type κ}
    → {P : ∀ U → (O U → A') → Type ℓ'} {Q : ∀ U → (O U → B') → Type ℓ'}
    → (O≃ : ∀ {U} → ob∣ U ∣ ≃ O U) {A B : CPSh.Ob {κ}}
    → (A≃ : A ʻ ⋆ ≃ A') (B≃ : B ʻ ⋆ ≃ B')
    → (∀ {U} → is-conc-section A ≃[ →-ap O≃ A≃ ] P U)
    → (∀ {U} → is-conc-section B ≃[ →-ap O≃ B≃ ] Q U)
    → Cpsh-hom A B ≃ ∫ₚ (is-cpsh-hom' P Q)
  Cpsh-hom≃Cpsh-hom' O≃ {A} A≃ B≃ Asec≃ Bsec≃ =
    Iso→Equiv Cpsh-hom-record-iso ∙e
    Σ-ap (→-ap A≃ B≃) λ f → Π'-ap-cod λ U →
      Π-ap-dom (section≃conc-section A e⁻¹) ∙e curry≃ ∙e
      Π-ap-dom (→-ap O≃ A≃ e⁻¹) ∙e Π-ap-cod λ g →
      Π-ap-dom (Asec≃ _ g (Equiv.ε (→-ap O≃ A≃) g) e⁻¹) ∙e
      Π-ap-cod λ Hg → Bsec≃ _ (Equiv.to (→-ap A≃ B≃) f ⊙ g) $ ext λ x →
        let g-sec : is-conc-section A (Equiv.from (→-ap O≃ A≃) g)
            g-sec = Equiv.from (Asec≃ _ g (Equiv.ε (→-ap O≃ A≃) g)) Hg
        in
        ap (Equiv.to B≃ ⊙ f) $
          ap fst (Equiv.ε (section≃conc-section A) (_ , g-sec)) $ₚ Equiv.from O≃ x ∙
          ap (Equiv.from A≃ ⊙ g) (Equiv.ε O≃ x)


  -- Representable presheaves are concrete
  Conc-よ₀ : (U : ⌞ C ⌟) → CPSh.Ob
  Conc-よ₀ U = よ₀ U , ⋆-hom-faithful

  -- Note: it holds definitionally that
  --                     Conc-よ₀ U ʻ ⋆ ≡ ob∣ U ∣
  -- is-conc-section (Conc-よ₀ U) {V} f ≡ is-conc-hom V U f

  opaque
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

  module _ where
    open Cartesian-category
    open is-product
    open Product
    open Terminal

    よ⋆-is-terminal : is-terminal (ConcPSh ℓ Conc) (Conc-よ₀ ⋆)
    よ⋆-is-terminal X =
      contr→is-terminal-PSh ℓ C (よ₀ ⋆) ⦃ basic-instance 0 (⋆-is-terminal _) ⦄ (X .fst)

    ConcPSh-terminal : Terminal (ConcPSh ℓ Conc)
    ConcPSh-terminal .top  = Conc-よ₀ ⋆
    ConcPSh-terminal .has⊤ = よ⋆-is-terminal

    ConcPSh-products : has-products (ConcPSh ℓ Conc)
    ConcPSh-products (A , aconc) (B , bconc) = prod where
      prod' = PSh-products _ C A B

      prod : Product (ConcPSh ℓ Conc) _ _
      prod .apex .fst = prod' .apex
      prod .apex .snd = is-concrete-limit
        {F = 2-object-diagram _ _} {ψ = 2-object-nat-trans _ _}
        (is-product→is-limit (PSh _ C) (prod' .has-is-product))
        λ { true → aconc ; false → bconc }
      prod .π₁                     = prod' .π₁
      prod .π₂                     = prod' .π₂
      prod .has-is-product .⟨_,_⟩  = prod' .⟨_,_⟩
      prod .has-is-product .π₁∘⟨⟩  = prod' .π₁∘⟨⟩
      prod .has-is-product .π₂∘⟨⟩  = prod' .π₂∘⟨⟩
      prod .has-is-product .unique = prod' .unique

    ConcPSh-cartesian : Cartesian-category (ConcPSh ℓ Conc)
    ConcPSh-cartesian .terminal = ConcPSh-terminal
    ConcPSh-cartesian .products = ConcPSh-products

  open Cartesian-category ConcPSh-cartesian hiding (!-unique₂)

  -- Note: It holds definitionally that
  --      top ʻ ⋆ ≡ ob∣ ⋆ ∣
  -- (A ⊗₀ B) ʻ ⋆ ≡ A ʻ ⋆ × B ʻ ⋆

  ⊗-sec-equiv
    : ∀ {U} {A B : CPSh.Ob} (f : ob∣ U ∣ → A ʻ ⋆ × B ʻ ⋆)
    → is-conc-section (A ⊗₀ B) f ≃ (is-conc-section A (fst ⊙ f) × is-conc-section B (snd ⊙ f))
  ⊗-sec-equiv f .fst = λ ((au , bu) , Hf) → (au , ap (fst ⊙_) Hf) , (bu , ap (snd ⊙_) Hf)
  ⊗-sec-equiv f .snd = is-iso→is-equiv $
    iso (λ ((au , Hfl) , (bu , Hfr)) → (au , bu) , funext λ _ → Hfl $ₚ _ ,ₚ Hfr $ₚ _)
      (λ _ → (refl ,ₚ prop!) ,ₚ (refl ,ₚ prop!))
      (λ _ → refl ,ₚ prop!)

  private
    module ip {n} (F : Fin n → CPSh.Ob) =
      Indexed-product
        (Cartesian→standard-finite-products ConcPSh-terminal ConcPSh-products F)

  Π-underlying : ∀ {n} (F : Fin n → CPSh.Ob) → ip.ΠF F ʻ ⋆ ≃ ∀ i → F i ʻ ⋆
  Π-underlying {zero} F = is-contr→≃ (⋆-is-terminal ⋆) (Π-dom-empty-is-contr λ ())
  Π-underlying {suc zero} F =
    Σ-contr-snd (λ _ → Π-dom-empty-is-contr λ ()) e⁻¹ ∙e Fin-suc-Π e⁻¹
  Π-underlying {suc (suc n)} F =
    Σ-ap-snd (λ _ → Π-underlying (F ⊙ fsuc)) ∙e Fin-suc-Π e⁻¹

  Π-sec-equiv
    : ∀ {n} {U} (F : Fin n → CPSh.Ob)
    → is-conc-section (ip.ΠF F) {U} ≃[ →-ap id≃ (Π-underlying F) ]
      (λ f → ∀ i → is-conc-section (F i) (λ x → f x i))
  Π-sec-equiv {zero} F _ _ _ =
    Σ-contr-fst (⋆-is-terminal _) ∙e
    is-contr→≃
      (is-prop→pathp-is-contr (λ _ → Π-is-hlevel 1 λ _ → !-unique₂) _ _)
      (Π-dom-empty-is-contr λ ())
  Π-sec-equiv {suc zero} F = over-left→over (→-ap id≃ (Π-underlying F)) λ f →
    Σ-contr-snd (λ _ → Π-dom-empty-is-contr λ ()) e⁻¹ ∙e Fin-suc-Π e⁻¹
  Π-sec-equiv {suc (suc n)} F = over-left→over (→-ap id≃ (Π-underlying F)) λ f →
    ⊗-sec-equiv {A = F fzero} {ip.ΠF (F ⊙ fsuc)} f ∙e
    Σ-ap-snd (λ _ → Π-sec-equiv (F ⊙ fsuc) _ _ refl) ∙e Fin-suc-Π e⁻¹


  module _ {o' ℓ'} {D : Precategory o' ℓ'} (ConcD : Conc-category D) where
    private module CD = Conc-category ConcD

    conc-dir-image
      : ∀ {κ} (F : Functor D C)
      → (F .F₀ CD.⋆ C.≅ ⋆) → (∀ {U} → is-surjective (F .F₁ {CD.⋆} {U}))
      → Functor (ConcPSh κ Conc) (ConcPSh κ ConcD)
    conc-dir-image {κ} F α F-onto-points = F' where
      G : Functor (PSh κ C) (PSh κ D)
      G = precompose (op F)

      opaque
        G-concrete : ∀ A → is-concrete Conc A → is-concrete ConcD (G .F₀ A)
        G-concrete A conc {U} {x} {y} H≡ = conc $ funext λ f →
          let module A = Fr A in
          case F-onto-points (f C.∘ α .to) of λ g p →
            A ⟪ f ⟫ x                           ≡⟨ A.expand (C.insertr (α .inverses .invl)) $ₚ x ⟩
            A ⟪ α .from ⟫ (A ⟪ f C.∘ α .to ⟫ x) ≡⟨ ap (A ⟪ _ ⟫_) (sym A.⟨ p ⟩ $ₚ x ∙ H≡ $ₚ g ∙ A.⟨ p ⟩ $ₚ y) ⟩
            A ⟪ α .from ⟫ (A ⟪ f C.∘ α .to ⟫ y) ≡⟨ A.collapse (C.cancelr (α .inverses .invl)) $ₚ y ⟩
            A ⟪ f ⟫ y                           ∎

      F' : Functor (ConcPSh κ Conc) (ConcPSh κ ConcD)
      F' .F₀ (A , conc) = G .F₀ A , G-concrete A conc
      F' .F₁            = G .F₁
      F' .F-id          = G .F-id
      F' .F-∘           = G .F-∘


module _ {ℓ} {C : Precategory ℓ ℓ} (Conc : Conc-category C) where
  open Conc-category Conc
  open Hom C
  open Cr._≅_

  private
    module C = Cr C
    module CPSh = Cr (ConcPSh ℓ Conc)

  module _ where
    open Cartesian-closed
    open Exponential
    open is-exponential

    opaque
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
      exp .B^A .fst             = exp' .B^A
      exp .B^A .snd             = is-concrete-exponential A B bconc
      exp .ev                   = exp' .ev
      exp .has-is-exp .ƛ        = exp' .ƛ
      exp .has-is-exp .commutes = exp' .commutes
      exp .has-is-exp .unique   = exp' .unique

  open Monoidal-category (Cartesian-monoidal (ConcPSh-cartesian Conc))
  open Cartesian-closed ConcPSh-closed

  ⇒-underlying : {A B : CPSh.Ob} → [ A , B ] ʻ ⋆ ≃ CPSh.Hom A B
  ⇒-underlying {A} {B} = _∘nt λ→ {A} ,
    CPSh.invertible-precomp-equiv {A} {Unit ⊗ A} {B} (CPSh.iso→invertible λ≅)

  open Cpsh-hom

  ⇒-sec-equiv
    : ∀ {U} (A B : CPSh.Ob)
    → is-conc-section Conc [ A , B ] {U} ≃[ →-ap id≃ (⇒-underlying {A} {B} ∙e Hom≃Cpsh-hom Conc {A = A} {B}) ]
      is-cpsh-hom Conc (Conc-よ₀ Conc U ⊗ A) B ⊙ uncurry ⊙ (to ⊙_)
  ⇒-sec-equiv {U} A B = prop-over-ext
    (→-ap id≃ (⇒-underlying {A} {B} ∙e Hom≃Cpsh-hom Conc))
    (λ {b} → is-conc-section-prop Conc [ A , B ] b)
    (λ {b} → is-cpsh-hom-prop Conc (Conc-よ₀ Conc U ⊗ A) B (uncurry (to ⊙ b)))
    (λ f (abu , p) {V} (uv , av) → abu .η _ (uv , av) , ext λ v →
      ap (λ f → f (uv C.∘ v) .η ⋆ _) p ∙
      ap (λ g → abu .η ⋆ g) (C.elimr (!-unique₂ _ _) ,ₚ refl) ∙
      abu .is-natural _ _ _ $ₚ _)
    (λ f Hf → Cpsh-hom→Hom Conc {A = Conc-よ₀ Conc U ⊗ A} {B}
      (conc-hom (uncurry (to ⊙ f)) λ au → Hf au) ,
      ext λ u V x av → B .snd $ ext λ z →
        sym (f u .is-hom av .snd) $ₚ z ∙
        ap (λ u → f u .to _) (C.insertr (!-unique₂ _ _)) ∙
        Hf (u C.∘ x , av) .snd $ₚ z)
