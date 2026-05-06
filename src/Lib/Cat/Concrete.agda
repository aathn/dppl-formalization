open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Exponential
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Total
open import Cat.Displayed.Thin
open import Cat.Cartesian
open import Cat.Prelude

open import Data.Fin.Base
open import Data.Power

module Lib.Cat.Concrete where

-- We give an explicit definition of concrete presheaves and show that the category
-- of concrete presheaves is cartesian closed.

open ∫Hom

module Conc-psh {κ o} {S : Type κ → Type o} (spec : Thin-structure κ S) where

  private
    C : Precategory (lsuc κ ⊔ o) κ
    C = Structured-objects spec
    module C = Precategory C
    module C-str = Thin-structure spec

  -- This definition is as presented in e.g., Matache et al. 2022.  It's equivalent
  -- to the standard definition when C's underlying sets are represented by a
  -- terminal object, as is traditionally assumed (and as in our applications).
  record CPSh-on (X : Type κ) : Type (lsuc κ ⊔ o) where
    no-eta-equality
    field
      is-sec : (U : C.Ob) → ℙ (⌞ U ⌟ → X)
      is-sec-∘
        : ∀ {U V} (g : ⌞ V ⌟ → X) (h : C.Hom U V)
        → ∣ is-sec V g ∣ → ∣ is-sec U (g ⊙ fst h) ∣
      pt-sec : ∀ {U} (x : X) → ∣ is-sec U (λ _ → x) ∣

  open CPSh-on

  is-cpsh-hom
    : {X Y : Type κ} (f : X → Y) (A : CPSh-on X) (B : CPSh-on Y) → Prop _
  is-cpsh-hom {X} f A B =
    el! $ ∀ {U} (g : ⌞ U ⌟ → X) → ∣ A .is-sec U g ∣ → ∣ B .is-sec U (f ⊙ g) ∣

  CPSh-structure : Thin-structure _ CPSh-on
  CPSh-structure .Thin-structure.is-hom                  = is-cpsh-hom
  CPSh-structure .Thin-structure.id-is-hom g Hg          = Hg
  CPSh-structure .Thin-structure.∘-is-hom f g Hf Hg h Hh = Hf (g ⊙ h) (Hg h Hh)

  CPSh : Precategory _ _
  CPSh = Structured-objects CPSh-structure

  ⊤CPSh : CPSh-on (Lift _ ⊤)
  ⊤CPSh .is-sec _ _ = ⊤Ω
  ⊤CPSh .is-sec-∘   = _
  ⊤CPSh .pt-sec     = _

  CPSh-terminal : Terminal CPSh
  CPSh-terminal .Terminal.top    = el! _ , ⊤CPSh
  CPSh-terminal .Terminal.has⊤ X =
    contr (∫hom (λ _ → lift tt) _) λ _ → ext λ _ → refl

  _×CPSh_ : {X Y : Type κ} → CPSh-on X → CPSh-on Y → CPSh-on (X × Y)
  (A ×CPSh B) .is-sec U f =
    A .is-sec U (fst ⊙ f) ∧Ω B .is-sec U (snd ⊙ f)
  (A ×CPSh B) .is-sec-∘ g h Hg =
    A .is-sec-∘ (fst ⊙ g) h (Hg .fst) , B .is-sec-∘ (snd ⊙ g) h (Hg .snd)
  (A ×CPSh B) .pt-sec x = A .pt-sec (fst x) , B .pt-sec (snd x)

  CPSh-products : (A B : ⌞ CPSh ⌟) → Product CPSh A B
  CPSh-products A B = prod where
    open Product
    open is-product
    prod : Product CPSh A B
    prod .apex = el! _ , A .snd ×CPSh B .snd
    prod .π₁ = ∫hom fst λ _ → fst
    prod .π₂ = ∫hom snd λ _ → snd
    prod .has-is-product .⟨_,_⟩ f g =
      ∫hom (λ z → f .fst z , g .fst z) λ h z → f .snd h z , g .snd h z
    prod .has-is-product .π₁∘⟨⟩ = ext λ _ → refl
    prod .has-is-product .π₂∘⟨⟩ = ext λ _ → refl
    prod .has-is-product .unique p q = ext λ _ → ap fst p $ₚ _ ,ₚ ap fst q $ₚ _

  CPSh-cartesian : Cartesian-category CPSh
  CPSh-cartesian .Cartesian-category.terminal = CPSh-terminal
  CPSh-cartesian .Cartesian-category.products = CPSh-products

  ΠCPSh : ∀ {n} {F : Fin n → Type κ} (As : ∀ i → CPSh-on (F i)) → CPSh-on (∀ i → F i)
  ΠCPSh As .is-sec U f      = ∀Ω _ λ i → As i .is-sec U (λ z → f z i)
  ΠCPSh As .is-sec-∘ g h Hg = inc λ i → As i .is-sec-∘ (λ z → g z i) h (□-out! Hg i)
  ΠCPSh As .pt-sec x        = inc λ i → As i .pt-sec (x i)

  CPSh-ip : ∀ {n} (F : Fin n → ⌞ CPSh ⌟) → Indexed-product CPSh F
  CPSh-ip F = ip where
    open Indexed-product
    open is-indexed-product
    ip : Indexed-product CPSh F
    ip .ΠF                 = el! _ , ΠCPSh (snd ⊙ F)
    ip .π i                = ∫hom (λ z → z i) (λ _ z → □-out! z i)
    ip .has-is-ip .tuple f = ∫hom (λ z i → f i .fst z) λ g z → inc λ i → f i .snd g z
    ip .has-is-ip .commute    = ext λ _ → refl
    ip .has-is-ip .unique f p = ext λ x i → ap fst (p i) $ₚ x

  module Repr-conc
    (const : {U V : C.Ob} (x : ⌞ V ⌟) → ∣ C-str.is-hom (λ _ → x) (U .snd) (V .snd) ∣)
    where

    repr₀ : (U : C.Ob) → CPSh-on ⌞ U ⌟
    repr₀ U .is-sec V f      = elΩ ∣ C-str.is-hom f (V .snd) (U .snd) ∣
    repr₀ U .is-sec-∘ g h Hg = inc (C-str.∘-is-hom g (h .fst) (□-out! Hg) (h .snd))
    repr₀ U .pt-sec {V} x    = inc (const {V} {U} x)

    repr : Functor C CPSh
    repr .Functor.F₀ U = U .fst , repr₀ U
    repr .Functor.F₁ f = ∫hom (f .fst) λ g Hg →
      inc (C-str.∘-is-hom _ _ (f .snd) (□-out! Hg))
    repr .Functor.F-id    = ext λ _ → refl
    repr .Functor.F-∘ f g = ext λ _ → refl

    _⇒CPSh_
      : {X Y : Type κ} (A : CPSh-on X) (B : CPSh-on Y)
      → CPSh-on (Σ[ f ∈ (X → Y) ] □ ∣ is-cpsh-hom f A B ∣)
    (A ⇒CPSh B) .is-sec U f =
      elΩ ∣ is-cpsh-hom (uncurry (fst ⊙ f)) (repr₀ U ×CPSh A) B ∣
    (A ⇒CPSh B) .is-sec-∘ g h Hg = inc λ f Hf → □-out! Hg _
      $ inc (C-str.∘-is-hom (h .fst) (fst ⊙ f) (h .snd) (□-out! (Hf .fst))) , Hf .snd
    (A ⇒CPSh B) .pt-sec f = inc λ g Hg → □-out! (f .snd) (snd ⊙ g) (Hg .snd)

    CPSh-closed : Cartesian-closed CPSh CPSh-cartesian
    CPSh-closed .Cartesian-closed.has-exp A B = exp where
      open Exponential
      open is-exponential
      exp : Exponential CPSh CPSh-cartesian A B
      exp .B^A = el! _ , A .snd ⇒CPSh B .snd
      exp .ev  = ∫hom (λ (f , x) → f · x) λ g Hg →
        □-out! (Hg .fst) (λ z → z , g z .snd) (inc C-str.id-is-hom , Hg .snd)
      exp .has-is-exp .ƛ {X , Γ} (∫hom f Hf) = ∫hom
        (λ x → (λ z → f (x , z)) , inc λ g Hg → Hf _ (Γ .pt-sec x , Hg))
        λ g Hg → inc λ h Hh →
          Hf _ (Γ .is-sec-∘ g (∫hom _ (□-out! (Hh .fst))) Hg , Hh .snd)
      exp .has-is-exp .commutes m = ext λ _ _ → refl
      exp .has-is-exp .unique _ p = ext λ _ _ → ap fst p $ₚ _
