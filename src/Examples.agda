open import Lib.Reals

module Examples (R : Reals₀) where

open import Syntax R
open import Typing R
open import Properties.Syntax R
open import Properties.Typing R

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.BindingSignature
open import Lib.LocallyNameless.AbstractionConcretion renaming (abs to acabs)
open import Lib.Env
open import Lib.Util

open import Data.Product.Instances using (Σ-≡-isDecEquivalence)
open import Data.List.Relation.Binary.Sublist.DecPropositional {A = 𝔸 × Type} _≐_
  using (_⊆_ ; [] ; _∷_ ; _∷ʳ_ ; _⊆?_)
open import Relation.Nullary using (True)

distinct? : (Γ : TyEnv) → Dec (Distinct Γ)
distinct? [] = yes []
distinct? (Γ , x ∶ T) with x ∈? dom Γ | distinct? Γ
... | yes p | _     = no λ { (H ∷ _) → ∉→¬∈ {{p = H}} p }
... | no  q | no  u = no λ { (_ ∷ H) → u H }
... | no  q | yes v = yes (¬∈→∉ q ∷ v)

-- Syntax shorthands

abs′ : 𝔸 → Type → Term → Term
abs′ x T t = abs T ▸ λ {₀ → acabs x t}

app′ : Term → Term → Term
app′ t₁ t₂ = app ▸ λ {₀ → t₁ ; ₁ → t₂}

let′ : 𝔸 → Type → Term → Term → Term
let′ x T t₁ t₂ = app′ (abs′ x T t₂) t₁

_+ᵖ_ : Term → Term → Term
t₁ +ᵖ t₂ = prim padd ▸ λ {₀ → t₁ ; ₁ → t₂}

proj′ : (n : ℕ) → Fin n → Term → Term
proj′ n i t = proj n i ▸ λ {₀ → t}

assume′ : Term → Term
assume′ t = assume ▸ λ {₀ → t}

weight′ : Term → Term
weight′ t = weight ▸ λ {₀ → t}

tvar′ :
  {x : 𝔸}
  (_ : [ x ∶ T ] ⊆ Γ)
  (_ : Distinct Γ)
  → -------------------
  Γ ⊢ fvar x :[ det ] T
tvar′ p q = tweaken tvar p q

tabs′ :
  {Γ : TyEnv}
  {T₁ T₂ : Type}
  {e : Eff}
  {t : Vector Term 1}
  (_ : (x : 𝔸) {{_ : x ∉ dom Γ}} → Γ , x ∶ T₁ ⊢ conc (t ₀) x :[ e ] T₂)
  → -------------------------------------------------------------------
  Γ ⊢ abs T₁ ▸ t :[ det ] T₁ ⇒[ e ] T₂
tabs′ {Γ} {t = t} hastype = tabs (Иi (dom Γ) hastype)

tlet′ :
  {Γ : TyEnv}
  {T₁ T₂ : Type}
  {e : Eff}
  {ts : Vector Term 2}
  {t : Vector Term 1}
  {{Heq : abs T₁ ▸ t ≡ ts ₀}}
  (_ : Γ ⊢ ts ₁ :[ e ] T₁)
  (_ : (y : 𝔸) {{_ : y ∉ dom Γ}} → Γ , y ∶ T₁ ⊢ conc (t ₀) y :[ e ] T₂)
  → -------------------------------------------------------------------
  Γ ⊢ app ▸ ts :[ e ] T₂
tlet′ {{Heq}} hastype₁ hastype₂ =
  tapp (tsub (subst (λ t → _ ⊢ t :[ _ ] _) Heq (tabs′ hastype₂)) 0≤ sub-refl)
       hastype₁

-- Variables

x y z f w β θ MODEL : 𝔸
x = new Ø
y = new [ x ]
z = new [ y ]
f = new [ z ]
w = new [ f ]
β = new [ w ]
θ = new [ β ]
MODEL = new [ θ ]

private
  instance
    distinct-dec : {Γ : TyEnv} {{_ : True (distinct? Γ)}} → Distinct Γ
    distinct-dec {Γ} with yes p ← distinct? Γ = p

    ⊆-dec : {Γ Γ′ : TyEnv} {{_ : True (Γ ⊆? Γ′)}} → Γ ⊆ Γ′
    ⊆-dec {Γ} {Γ′} with yes p ← Γ ⊆? Γ′ = p

-- Examples

ex1 :
  [] ⊢ abs′ x (treal A) (fvar x) :[ det ] (treal A ⇒[ det ] treal A)
ex1 = tabs′ (λ _ → tvar′ (refl ∷ []) it)

Ts : Coeff → Vector Type 2
Ts c ₀ = treal N
Ts c ₁ = treal c

ex2 : ∀ c → 
  [ w ∶ treal N ⇒[ det ] treal N ] ⊢
    abs′ z (ttup 2 (Ts c))
      (let′ x (treal N) (proj′ 2 ₀ (fvar z))
      (let′ y (treal c) (proj′ 2 ₁ (fvar z))
      (app′ (fvar w) (fvar x) +ᵖ fvar y)))
  :[ det ] ttup 2 (Ts c) ⇒[ det ] treal A
ex2 c =
  tabs′ λ z {{H∉z}} →
    tlet′ (tproj ₀ (tvar′ (refl ∷ it) (H∉z ∷ it))) λ x {{H∉x}} →
    tlet′ (tproj ₁ (tvar′ (_ ∷ʳ refl ∷ it) (H∉x ∷ H∉z ∷ it))) λ y {{H∉y}} →
    let Hd = H∉y ∷ H∉x ∷ H∉z ∷ it in
    tprim refl Hd λ where
      ₀ → tsub (tapp (tvar′ (_ ∷ʳ _ ∷ʳ _ ∷ʳ refl ∷ it) Hd)
                     (tvar′ (_ ∷ʳ refl ∷ it) Hd))
               ≤refl (sreal 0≤)
      ₁ → tsub (tvar′ (refl ∷ it) Hd) ≤refl (sreal 0≤)
