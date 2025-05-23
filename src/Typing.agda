open import Lib.Reals

module Typing (R : Reals₀) where

open Reals R
open import Syntax R

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.AbstractionConcretion hiding (abs)
open import Lib.BindingSignature

open import Data.List using (map)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Unary.All using (All)

TyEnv : Set
TyEnv = List (𝔸 × Type)

variable
  Γ Γ′ : TyEnv

infixl 5 _,_∶_
pattern [_∶_]   x T = (x , T) ∷ []
pattern _,_∶_ Γ x T = (x , T) ∷ Γ

dom : TyEnv → Fset 𝔸
dom [] = Ø
dom (Γ , x ∶ _) = [ x ] ∪ dom Γ

data Distinct : TyEnv → Set where
  []  : Distinct []
  _∷_ : {x : 𝔸} → x ∉ dom Γ → Distinct Γ → Distinct (Γ , x ∶ T)

PrimTy : (ϕ : Prim) → Vector Coeff (PrimAr ϕ) × Coeff
PrimTy padd        = const A , A
PrimTy pmul        = const A , A
PrimTy psin        = const A , A
PrimTy (pwiener r) = const N , N

DistTy : (D : Dist) → Vector Coeff (DistAr D) × Type
DistTy dnormal = const N , treal N
DistTy dbeta   = const N , treal N
DistTy dwiener = (λ()) , (treal N ⇒[ det ] treal N)

_⊙_ : Coeff → Type → Type
c ⊙ (treal c′) = treal (c ⊔′ c′)
c ⊙ (ttup n Ts) = ttup n $ c ⊙_ ∘ Ts
c ⊙ T          = T

_≤ᶜ_ : Coeff → Type → Set
c ≤ᶜ treal d = c ≤′ d
c ≤ᶜ ttup n Ts = ∀ i → c ≤ᶜ Ts i
c ≤ᶜ T = 𝟙

_≤ᴱ_ : Coeff → TyEnv → Set
c ≤ᴱ Γ = All (c ≤ᶜ_ ∘ π₂) Γ

infix 5 _<:_
data _<:_ : Type → Type → Set where

  sreal :
    (_ : c′ ≤′ c)
    → -----------------
    treal c <: treal c′

  stup :
    {Ts Ts′ : Vector Type n}
    (_ : ∀ i → Ts i <: Ts′ i)
    → -----------------------
    ttup n Ts <: ttup n Ts′

  sarr :
    {T₁ T₁′ T₂ T₂′ : Type}
    (_ : T₁′ <: T₁)
    (_ : T₂ <: T₂′)
    (_ : e ≤′ e′)
    → -----------------------------
    T₁ ⇒[ e ] T₂ <: T₁′ ⇒[ e′ ] T₂′

  sdist :
    (_ : T <: T′)
    → -----------------
    tdist T <: tdist T′


_<:ᴱ_ : TyEnv → TyEnv → Set
_<:ᴱ_ = Pointwise (λ (x₁ , T₁) (x₂ , T₂) → x₁ ≡ x₂ × T₁ <: T₂)


infix 4 _⊢_:[_]_
data _⊢_:[_]_ : TyEnv → Term → Eff → Type → Set where

  tvar :
    {x : 𝔸}
    → ---------------------------
    [ x ∶ T ] ⊢ fvar x :[ det ] T

  tabs :
    {T₁ T₂ : Type}
    {t : Vector Term 1}
    (_ : И x ∶ 𝔸 , Γ , x ∶ T₁ ⊢ conc (t ₀) x :[ e ] T₂)
    → -------------------------------------------------
    Γ ⊢ abs T₁ ▸ t :[ det ] T₁ ⇒[ e ] T₂

  tapp :
    {T₁ T₂ : Type}
    {ts : Vector Term 2}
    (_ : Γ ⊢ ts ₀ :[ e ] T₁ ⇒[ e ] T₂)
    (_ : Γ ⊢ ts ₁ :[ e ] T₁)
    → --------------------------------
    Γ ⊢ app ▸ ts :[ e ] T₂

  tprim :
    {cs : Vector Coeff (PrimAr ϕ)}
    {ts : Vector Term (PrimAr ϕ)}
    (_ : PrimTy ϕ ≡ (cs , c))
    (_ : Distinct Γ)
    (_ : ∀ i → Γ ⊢ ts i :[ e ] treal (cs i))
    → --------------------------------------
    Γ ⊢ prim ϕ ▸ ts :[ e ] treal c

  treal :
    --------------------------
    [] ⊢ real r :[ det ] treal N

  ttup :
    {Ts : Vector Type n}
    {ts : Vector Term n}
    (_ : Distinct Γ)
    (_ : ∀ i → Γ ⊢ ts i :[ e ] Ts i)
    → ------------------------------
    Γ ⊢ tup n ▸ ts :[ e ] ttup n Ts

  tproj :
    {Ts : Vector Type n}
    {t : Vector Term 1}
    (i : Fin n)
    (_ : Γ ⊢ t ₀ :[ e ] ttup n Ts)
    → ----------------------------
    Γ ⊢ proj n i ▸ t :[ e ] Ts i

  tif :
    {ts : Vector Term 3}
    (_ : Γ ⊢ ts ₀ :[ e ] treal P)
    (_ : Γ ⊢ ts ₁ :[ e ] T)
    (_ : Γ ⊢ ts ₂ :[ e ] T)
    → ---------------------------
    Γ ⊢ if ▸ ts :[ e ] T

  tdiff :
    {ts : Vector Term 2}
    {cs : Vector Coeff n}
    {ds : Vector Coeff m}
    (_ : ∀ i → cs i ≤′ P)
    (_ : Γ ⊢ ts ₀ :[ e ] treals n cs ⇒[ det ] treals m ds)
    (_ : Γ ⊢ ts ₁ :[ e ] treals n cs)
    → ----------------------------------------------------------
    Γ ⊢ diff ▸ ts :[ e ] treals n (const A) ⇒[ det ] treals m ds

  tsolve :
    {ts : Vector Term 3}
    {cs : Vector Coeff n}
    (_ : Γ ⊢ ts ₀ :[ e ] ttup 2 (λ {₀ → treal c; ₁ → treals n cs}) ⇒[ det ] treals n cs)
    (_ : Γ ⊢ ts ₁ :[ e ] treals n cs)
    (_ : Γ ⊢ ts ₂ :[ e ] treal c)
    → P ≤′ c
    → --------------------------------------------------------------------------------
    Γ ⊢ solve ▸ ts :[ e ] treals n cs

  tdist :
    {cs : Vector Coeff (DistAr D)}
    {ts : Vector Term (DistAr D)}
    (_ : DistTy D ≡ (cs , T))
    (_ : Distinct Γ)
    (_ : ∀ i → Γ ⊢ ts i :[ e ] treal (cs i))
    → --------------------------------------
    Γ ⊢ dist D ▸ ts :[ e ] tdist T

  tassume :
    {t : Vector Term 1}
    (_ : Γ ⊢ t ₀ :[ rnd ] tdist T)
    → ----------------------------
    Γ ⊢ assume ▸ t :[ rnd ] T

  tweight :
    {t : Vector Term 1}
    (_ : Γ ⊢ t ₀ :[ rnd ] treal N)
    → ----------------------------
    Γ ⊢ weight ▸ t :[ rnd ] tunit

  tinfer :
    {t : Vector Term 1}
    (_ : Γ ⊢ t ₀ :[ e ] tunit ⇒[ rnd ] T)
    (_ : N ≤ᴱ Γ)
    → -----------------------------------
    Γ ⊢ infer ▸ t :[ e ] tdist T

  tweaken :
    {t : Term}
    (_ : Γ′ ⊢ t :[ e ] T)
    (_ : Γ′ ⊆ Γ)
    (_ : Distinct Γ)
    → -------------------
    Γ ⊢ t :[ e ] T

  tsub :
    (_ : Γ ⊢ t :[ e ] T)
    (_ : e ≤′ e′)
    (_ : T <: T′)
    → ------------------
    Γ ⊢ t :[ e′ ] T′

  tpromote :
    (_ : Γ ⊢ t :[ e ] T)
    (_ : c ≤ᴱ Γ)
    → ------------------
    Γ ⊢ t :[ e ] c ⊙ T
