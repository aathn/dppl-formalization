open import Lib.Reals

module Examples (R : Reals₀) where

open import Syntax R
open import Typing R
open import Lib.Unfinite
open import Lib.Prelude
open import Lib.BindingSignature
open import Lib.AbstractionConcretion renaming (abs to acabs)
open import Data.List.Relation.Binary.Sublist.Propositional
-- open import Data.List.Relation.Binary.Sublist.DecPropositional {A = 𝔸}

-- Syntax shorthands

abs′ : 𝔸 → Type → Term → Term
abs′ x T t = abs T λ {₀ → acabs x t}

app‵ : Term → Term → Term
app‵ t₁ t₂ = app λ {₀ → t₁ ; ₁ → t₂}

let‵ : 𝔸 → Type → Term → Term → Term
let‵ x T t₁ t₂ = app‵ (abs′ x T t₂) t₁

_+ᵖ_ : Term → Term → Term
t₁ +ᵖ t₂ = prim padd λ {₀ → t₁ ; ₁ → t₂}

proj' : ∀ {n} → Fin n → Term → Term
proj' {n} i t = proj {n} i λ {₀ → t}

assume‵ : Term → Term
assume‵ t = assume λ {₀ → t}

weight‵ : Term → Term
weight‵ t = weight λ {₀ → t}

tabs‵ : ∀ {Γ T₁ T₂ e t} → 
  (∀ (x : 𝔸) → {{x ∉ fv (t ₀)}} → Γ , x ∶ T₁ ⊢ conc (t ₀) x :[ e ] T₂) →
  Γ ⊢ abs T₁ t :[ det ] T₁ ⇒[ e ] T₂
tabs‵ {t = t} hastype = tabs (Иi (fv (t ₀)) hastype)

-- Variables

_vars0 : Fset 𝔸
_vars0 = Ø

x : 𝔸
x = new _vars0
_vars1 : Fset 𝔸
_vars1 = _vars0 ∪ [ x ]

y : 𝔸
y = new _vars1
_vars2 : Fset 𝔸
_vars2 = _vars1 ∪ [ y ]

z : 𝔸
z = new _vars2
_vars3 : Fset 𝔸
_vars3 = _vars2 ∪ [ z ]

f : 𝔸
f = new _vars3
_vars4 : Fset 𝔸
_vars4 = _vars3 ∪ [ f ]

w : 𝔸
w = new _vars4
_vars5 : Fset 𝔸
_vars5 = _vars4 ∪ [ w ]

β : 𝔸
β = new _vars5
_vars6 : Fset 𝔸
_vars6 = _vars5 ∪ [ β ]

θ : 𝔸
θ = new _vars6
_vars7 : Fset 𝔸
_vars7 = _vars6 ∪ [ θ ]

MODEL : 𝔸
MODEL = new _vars7
_vars8 : Fset 𝔸
_vars8 = _vars7 ∪ [ MODEL ]

-- Examples

testExample :
  [] ⊢ abs′ x (treal A) (fvar x) :[ det ] (treal A ⇒[ det ] treal A)
testExample = tabs‵ (λ _ → tvar)

example10 : ∀ c → let T = ttup {2} (λ {₀ → treal N ; ₁ → treal c}) in
  [ w ∶ treal N ⇒[ det ] treal N ] ⊢
  abs′ z T
    (let‵ x (treal N) (proj' {2} ₀ (fvar z))
    (let‵ y (treal N) (proj' {2} ₁ (fvar z))
    (app‵ (fvar w) (fvar x) +ᵖ fvar y)))
  :[ det ] T ⇒[ det ] treal A
example10 c = 
  tabs‵ (λ _ → tapp 
           (tabs‵ (λ _ → tapp
                     (tabs‵ (λ _ →
                               tprim
                                 refl
                                 (λ {₀ → tapp {!!} {!!};₁ → {!!}})
                                 {!!}))
                     (tproj  ₁ (tweaken tvar {!!} {!!}))))
           (tproj ₀ (tweaken tvar (refl ∷ _ ∷ʳ []) {!!})))
