open import Lib.Reals

module Typing (R : Reals₀) where

open Reals R
open import Syntax R

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.AbstractionConcretion hiding (abs)
open import Lib.LocallyNameless.BindingSignature
open import Lib.Env

open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Unary.All using (All)

TyEnv : Set
TyEnv = Env Type

variable
  Γ Γ′ : TyEnv

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
c ⊙ treal c′ = treal (c ⊔′ c′)
c ⊙ ttup n Ts = ttup n $ c ⊙_ ∘ Ts
c ⊙ (T₁ ⇒[ e ] T₂) = (c ⊙ T₁) ⇒[ e ] (c ⊙ T₂)
c ⊙ tdist T = tdist T

_≤ᶜ_ : Coeff → Type → Set
c ≤ᶜ treal d = c ≤′ d
c ≤ᶜ ttup n Ts = ∀ i → c ≤ᶜ Ts i
c ≤ᶜ (T₁ ⇒[ _ ] T₂) = c ≤ᶜ T₁ × c ≤ᶜ T₂
c ≤ᶜ tdist T = 𝟙

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


infix 4 _⊢_:[_,_]_
data _⊢_:[_,_]_ : TyEnv → Term → Coeff → Eff → Type → Set where

  tvar :
    {x : 𝔸}
    (_ : [ x ∶ T ] ⊆ Γ)
    (_ : c ≤ᶜ T)
    (_ : Distinct Γ)
    → -----------------------
    Γ ⊢ fvar x :[ c , det ] T

  tabs :
    {T₁ T₂ : Type}
    {t : Vector Term 1}
    (_ : И x ∶ 𝔸 , Γ , x ∶ c ⊙ T₁ ⊢ conc (t ₀) x :[ c , e ] T₂)
    → ---------------------------------------------------------
    Γ ⊢ abs T₁ ▸ t :[ c , det ] T₁ ⇒[ e ] T₂

  tapp :
    {T₁ T₂ : Type}
    {ts : Vector Term 2}
    (_ : Γ ⊢ ts ₀ :[ c , e ] T₁ ⇒[ e ] T₂)
    (_ : Γ ⊢ ts ₁ :[ c , e ] T₁)
    → ------------------------------------
    Γ ⊢ app ▸ ts :[ c , e ] T₂

  tprim :
    {cs : Vector Coeff (PrimAr ϕ)}
    {ts : Vector Term (PrimAr ϕ)}
    (_ : PrimTy ϕ ≡ (cs , c′))
    (_ : Distinct Γ)
    (_ : ∀ i → Γ ⊢ ts i :[ c , e ] treal (cs i))
    → ------------------------------------------
    Γ ⊢ prim ϕ ▸ ts :[ c , e ] treal c′

  treal :
    (Hd : Distinct Γ)
    → -----------------------------
    Γ ⊢ real r :[ c , det ] treal A

  ttup :
    {Ts : Vector Type n}
    {ts : Vector Term n}
    (_ : Distinct Γ)
    (_ : ∀ i → Γ ⊢ ts i :[ c , e ] Ts i)
    → ----------------------------------
    Γ ⊢ tup n ▸ ts :[ c , e ] ttup n Ts

  tproj :
    {Ts : Vector Type n}
    {t : Vector Term 1}
    (i : Fin n)
    (_ : Γ ⊢ t ₀ :[ c , e ] ttup n Ts)
    → --------------------------------
    Γ ⊢ proj n i ▸ t :[ c , e ] Ts i

  tif :
    {ts : Vector Term 3}
    (_ : Γ ⊢ ts ₀ :[ P , e ] treal A)
    (_ : Γ ⊢ ts ₁ :[ c , e ] T)
    (_ : Γ ⊢ ts ₂ :[ c , e ] T)
    → -------------------------------
    Γ ⊢ if ▸ ts :[ c , e ] T

  tdiff :
    {ts : Vector Term 2}
    {cs : Vector Coeff n}
    {cs′ : Vector Coeff m}
    (_ : ∀ i → cs i ≤′ P)
    (_ : c ≤′ P)
    (_ : Γ ⊢ ts ₀ :[ c , e ] treals n cs ⇒[ det ] treals m cs′)
    (_ : Γ ⊢ ts ₁ :[ c , e ] treals n cs)
    → ---------------------------------------------------------------
    Γ ⊢ diff ▸ ts :[ c , e ] treals n (const A) ⇒[ det ] treals m cs′

  -- TODO: Fix the typing rule for solve 
  tsolve :
    {Γ : TyEnv}
    {ts : Vector Term 3}
    {cs : Vector Coeff n}
    {c₀ : Coeff}
    (_ : Γ ⊢ ts ₀ :[ c₀ , e ] (ttup 2 λ {₀ → treal c′; ₁ → treals n cs}) ⇒[ det ] treals n cs)
    (_ : Γ ⊢ ts ₁ :[ c₀ , e ] ttup 2 λ {₀ → treal c; ₁ → treals n cs})
    (_ : Γ ⊢ ts ₂ :[ c₀ , e ] treal c′)
    → ------------------------------------------------------------------------------------------------------
    Γ ⊢ solve ▸ ts :[ c₀ , e ] ttup 2 λ {₀ → treal c; ₁ → treals n cs}

  tdist :
    {cs : Vector Coeff (DistAr D)}
    {ts : Vector Term (DistAr D)}
    (_ : DistTy D ≡ (cs , T))
    (_ : Distinct Γ)
    (_ : ∀ i → Γ ⊢ ts i :[ c , e ] treal (cs i))
    → ------------------------------------------
    Γ ⊢ dist D ▸ ts :[ c , e ] tdist T

  tassume :
    {t : Vector Term 1}
    (_ : Γ ⊢ t ₀ :[ c , rnd ] tdist T)
    → --------------------------------
    Γ ⊢ assume ▸ t :[ c , rnd ] T

  tweight :
    {t : Vector Term 1}
    (_ : Γ ⊢ t ₀ :[ N , rnd ] treal A)
    → --------------------------------
    Γ ⊢ weight ▸ t :[ c , rnd ] tunit

  tinfer :
    {t : Vector Term 1}
    (_ : Γ ⊢ t ₀ :[ N , e ] tunit ⇒[ rnd ] T)
    → ---------------------------------------
    Γ ⊢ infer ▸ t :[ c , e ] tdist T

  tsub :
    (_ : Γ ⊢ t :[ c , e ] T)
    (_ : e ≤′ e′)
    (_ : T <: T′)
    → ----------------------
    Γ ⊢ t :[ c , e′ ] T′

  tpromote :
    (_ : Γ ⊢ t :[ c , e ] T)
    (_ : c′ ≤′ c)
    → ----------------------
    Γ ⊢ t :[ c′ ,  e ] c ⊙ T

  tdemote :
    (_ : Γ ⊢ t :[ c′ , e ] c ⊙ T)
    (_ : c′ ≤′ c)
    → ---------------------------
    Γ ⊢ t :[ c , e ] T
