open import Lib.Reals

module Examples (R : Reals₀) where

open import Syntax R
open import Typing R
open import Properties.Syntax R
open import Properties.Typing R
open import Properties.Util

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.BindingSignature
open import Lib.AbstractionConcretion renaming (abs to acabs)

open import Data.Product.Instances using (Σ-≡-isDecEquivalence)
open import Data.List.Relation.Binary.Sublist.DecPropositional {A = 𝔸 × Type} _≐_
  using (_⊆_ ; [] ; _∷_ ; _∷ʳ_ ; _⊆?_)
open import Relation.Nullary using (True)

distinct? : ∀ Γ → Dec (Distinct Γ)
distinct? [] = yes []
distinct? (Γ , x ∶ T) with x ∈? dom Γ | distinct? Γ
... | yes p | _     = no λ { (H ∷ _) → ∉→¬∈ {{p = H}} p }
... | no  q | no  u = no λ { (_ ∷ H) → u H}
... | no  q | yes v = yes (¬∈→∉ q ∷ v)

-- Syntax shorthands

abs′ : 𝔸 → Type → Term → Term
abs′ x T t = abs T λ {₀ → acabs x t}

app′ : Term → Term → Term
app′ t₁ t₂ = app λ {₀ → t₁ ; ₁ → t₂}

let′ : 𝔸 → Type → Term → Term → Term
let′ x T t₁ t₂ = app′ (abs′ x T t₂) t₁

_+ᵖ_ : Term → Term → Term
t₁ +ᵖ t₂ = prim padd λ {₀ → t₁ ; ₁ → t₂}

proj′ : ∀ {n} → Fin n → Term → Term
proj′ {n} i t = proj {n} i λ {₀ → t}

assume′ : Term → Term
assume′ t = assume λ {₀ → t}

weight′ : Term → Term
weight′ t = weight λ {₀ → t}

tvar′ :
  {x : 𝔸}
  {T : Type}
  {Γ : TyEnv}
  {{_ : True ([ x ∶ T ] ⊆? Γ)}}
  {{_ : True (distinct? Γ)}}
  → -------------------------
  Γ ⊢ fvar x :[ det ] T
tvar′ {x} {T} {Γ}
  with yes p ← [ x ∶ T ] ⊆? Γ | yes q ← distinct? Γ =
  tweaken tvar p q

tabs′ :
  {Γ : TyEnv}
  {T₁ T₂ : Type}
  {e : Eff}
  {t : Vector Term 1}
  {{vars : Fset 𝔸}}
  (_ : ∀ (x : 𝔸) {{_ : x ∉ vars ∪ fv (t ₀)}} → Γ , x ∶ T₁ ⊢ conc (t ₀) x :[ e ] T₂)
  → ------------------------------------------------------------------------
  Γ ⊢ abs T₁ t :[ det ] T₁ ⇒[ e ] T₂
tabs′ {t = t} {{vars}} hastype = tabs (Иi (vars ∪ fv (t ₀)) hastype)

tlet′ :
  {Γ : TyEnv}
  {x : 𝔸}
  {T₁ T₂ : Type}
  {e : Eff}
  {ts : Vector Term 2}
  {t : Vector Term 1}
  {{vars : Fset 𝔸}}
  {{Heq : abs T₁ t ≡ ts ₀}}
  (_ : Γ ⊢ ts ₁ :[ e ] T₁)
  (_ : ∀ (y : 𝔸) {{_ : y ∉ vars ∪ fv (t ₀)}} → Γ , y ∶ T₁ ⊢ conc (t ₀) y :[ e ] T₂)
  → -------------------------------------------------------------------------------
  Γ ⊢ app ts :[ e ] T₂
tlet′ {{vars}} {{Heq}} hastype₁ hastype₂ =
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
    vars : Fset 𝔸
    vars = [ MODEL ]

-- Examples

testExample :
  [] ⊢ abs′ x (treal A) (fvar x) :[ det ] (treal A ⇒[ det ] treal A)
testExample = tabs′ (λ _ → tvar)

Ts : Coeff → Vector Type 2
Ts c ₀ = treal N
Ts c ₁ = treal c

example10 : ∀ c → 
  [ w ∶ treal N ⇒[ det ] treal N ] ⊢
    abs′ z (ttup (Ts c))
      (let′ x (treal N) (proj′ {2} ₀ (fvar z))
      (let′ y (treal N) (proj′ {2} ₁ (fvar z))
      (app′ (fvar w) (fvar x) +ᵖ fvar y)))
  :[ det ] ttup (Ts c) ⇒[ det ] treal A
example10 c =
  tabs′ λ z →
    tlet′ (tproj {Ts = Ts c} ₀ (tweaken tvar {!!} {!!})) λ x →
    tlet′ (tproj ₁ (tweaken tvar {!!} {!!})) λ y →
    tprim refl {!!} λ where
      ₀ → tapp {!!} {!!} -- tvar′ tvar′
      ₁ → {!!} -- tvar′
