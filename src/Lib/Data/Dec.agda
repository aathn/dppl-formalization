module Lib.Data.Dec where

open import 1Lab.Prelude hiding (_≠_ ; _∉_)

open import Data.Dec.Base
open import Data.Bool.Base

module _ {ℓ : Level} {A : Type ℓ} where

  is-no : Dec A → Type
  is-no d = is-yes (Dec-→ ⦃ d ⦄ ⦃ Dec-⊥ ⦄)

  true→is-yes : {d : Dec A} → A → is-yes d
  true→is-yes {yes _} _ = tt
  true→is-yes {no ¬a} a = ¬a a

  false→is-no : {d : Dec A} → ¬ A → is-no d
  false→is-no {yes a} ¬a = ¬a a
  false→is-no {no _} ¬a = tt

  is-yes→true : {d : Dec A} → is-yes d → A
  is-yes→true {yes a} _ = a

  is-no→false : {d : Dec A} → is-no d → ¬ A
  is-no→false {no ¬a} _ = ¬a

  ifᵈ-yes : ∀ {ℓ'} {B : Type ℓ'} {x y : B} (d : Dec A) → is-yes d → (ifᵈ d then x else y) ≡ x
  ifᵈ-yes (yes _) _ = refl

  ifᵈ-no : ∀ {ℓ'} {B : Type ℓ'} {x y : B} (d : Dec A) → is-no d → (ifᵈ d then x else y) ≡ y
  ifᵈ-no (no _) _ = refl

  is-yes-is-prop : {d : Dec A} → is-prop (is-yes d)
  is-yes-is-prop {yes _} = hlevel 1
  is-yes-is-prop {no  _} = hlevel 1

  so→is-yes : {d : Dec A} → So (Dec→Bool d) → is-yes d
  so→is-yes {yes a} _ = tt
  so→is-yes {no ¬a} p = absurd (¬so-false p)

  is-yes→so : {d : Dec A} → is-yes d → So (Dec→Bool d)
  is-yes→so {yes a} _ = oh

  is-yes≃so : {d : Dec A} → is-yes d ≃ So (Dec→Bool d)
  is-yes≃so = prop-ext is-yes-is-prop (hlevel 1) is-yes→so so→is-yes

module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} ⦃ _ : Discrete A ⦄ where

  ifᵈ-≡ : {a b : A} {x y : B} → a ≡ b → (ifᵈ (a ≡? b) then x else y) ≡ x
  ifᵈ-≡ {a} {b} = ifᵈ-yes (a ≡? b) ∘ true→is-yes
  
  ifᵈ-≠ : {a b : A} {x y : B} → ¬ a ≡ b → (ifᵈ (a ≡? b) then x else y) ≡ y
  ifᵈ-≠ {a} {b} = ifᵈ-no (a ≡? b) ∘ false→is-no

module _ {ℓ : Level} {A : Type ℓ} ⦃ _ : Discrete A ⦄ where

  infix 4 _≠_
  _≠_ : (x y : A) → Type
  x ≠ y = is-no (x ≡? y)

  sym≠ : (x y : A) → x ≠ y → y ≠ x
  sym≠ x y H≠ with x ≡? y
  ... | yes p = absurd H≠
  ... | no ¬p = false→is-no (¬p ∘ sym)

  ¬≡→≠ : {x y : A} → ¬ x ≡ y → x ≠ y
  ¬≡→≠ = false→is-no

  ≠→¬≡ : {x y : A} → x ≠ y → ¬ x ≡ y
  ≠→¬≡ = is-no→false

  ¬≠ : (x : A) → ¬ (x ≠ x)
  ¬≠ x = flip ≠→¬≡ refl

module _ {ℓ : Level} {A B : Type ℓ} ⦃ _ : Discrete A ⦄ ⦃ _ : Discrete B ⦄ where

  inj≠ :
    {f : A → B}
    (injf : injective f)
    {x y : A}
    → ---------------
    x ≠ y → f x ≠ f y
  inj≠ injf p = ¬≡→≠ λ q → ≠→¬≡ p (injf q)

  ap≠ :
    {f : A → B}
    {x y : A}
    → -----------------
    f x ≠ f y → x ≠ y
  ap≠ {f} p = ¬≡→≠ λ q → ≠→¬≡ p (ap f q)

module _
  {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {ℙA : Type ℓ'}
  ⦃ m : Membership A ℙA ℓ'' ⦄ ⦃ _ : {x : A} {y : ℙA} → Dec (x ∈ y) ⦄ where

  _∉_ : A → ℙA → Type
  x ∉ y = is-no (holds? (x ∈ y))

  ¬∈→∉ : ∀ {x y} → ¬ x ∈ y → x ∉ y
  ¬∈→∉ = false→is-no

  ∉→¬∈ : ∀ {x y} → x ∉ y → ¬ x ∈ y
  ∉→¬∈ = is-no→false
