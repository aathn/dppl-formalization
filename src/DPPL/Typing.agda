open import Lib.Algebra.Reals

module DPPL.Typing (R : Reals₀) where

open Reals R hiding (_≤_)
open import DPPL.Syntax R
open import DPPL.Regularity

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.AbstractionConcretion
open import Lib.LocallyNameless.BindingSignature
open import Lib.Data.Vector
open import Lib.Syntax.Env

open import Order.Base
open import Order.Lattice

open VecSyntax
open Reg↓≤ renaming (_≤_ to _≤ᶜ_)
open Eff≤  renaming (_≤_ to _≤ᵉ_)
open is-lattice Reg↓-lattice

TyEnv : Type
TyEnv = Env Ty

module TypingVars where
  variable
    Γ Γ' : TyEnv
    a    : 𝔸

open SyntaxVars
open TypingVars
  
PrimTy : (ϕ : Prim) → Reg↓ ^ PrimAr ϕ × Reg↓
PrimTy padd    = make A↓ , A↓
PrimTy pmul    = make A↓ , A↓
PrimTy psin    = make A↓ , A↓
-- TODO: What regularities would be appropriate for pnormal/pbeta?
PrimTy pnormal = make M↓ , M↓
PrimTy pbeta   = make M↓ , M↓
PrimTy pwiener = lookup (M↓ ∷ C↓ ∷ []) , C↓

_⊙_ : Reg↓ → Ty → Ty
c ⊙ treal c'       = treal (c ∩ c')
c ⊙ ttup n Ts      = ttup n λ i → c ⊙ Ts i
c ⊙ (T₁ ⇒[ e ] T₂) = (c ⊙ T₁) ⇒[ e ] (c ⊙ T₂)
c ⊙ tdist T        = tdist T

_≤ᵗ_ : Ty → Reg↓ → Type
treal d        ≤ᵗ c = d ≤ᶜ c
ttup n Ts      ≤ᵗ c = ∀ i → Ts i ≤ᵗ c
(T₁ ⇒[ e ] T₂) ≤ᵗ c = T₁ ≤ᵗ c × T₂ ≤ᵗ c
tdist T        ≤ᵗ c = ⊤


infix 5 _<:_
data _<:_ : Ty → Ty → Type where

  sreal :
    (_ : c ≤ᶜ c')
    → -----------------
    treal c <: treal c'

  stup :
    {Ts Ts' : Ty ^ n}
    (_ : ∀ i → Ts i <: Ts' i)
    → -----------------------
    ttup n Ts <: ttup n Ts'

  sarr :
    {T₁ T₁' T₂ T₂' : Ty}
    (_ : T₁' <: T₁)
    (_ : T₂ <: T₂')
    (_ : e ≤ᵉ e')
    → -----------------------------
    T₁ ⇒[ e ] T₂ <: T₁' ⇒[ e' ] T₂'

  sdist :
    (_ : T <: T')
    → -----------------
    tdist T <: tdist T'


_<:ᵉ_ : TyEnv → TyEnv → Type
Γ <:ᵉ Γ' = ∀ {a T} → a ∶ T ∈ Γ → Σ[ T' ∈ Ty ] (a ∶ T' ∈ Γ') × (T <: T')


infix 4 _⊢_:[_,_]_
data _⊢_:[_,_]_ : TyEnv → Tm → Reg↓ → Eff → Ty → Type where

  tvar :
    (_ : a ∶ T ∈ Γ)
    (_ : T ≤ᵗ c)
    → -----------------------
    Γ ⊢ fvar a :[ c , det ] T

  tlam :
    {t : Tm ^ 1}
    (_ : И[ a ∈ 𝔸 ] (Γ , a ∶ T) ⊢ conc (t ₀) a :[ c , e ] T')
    → -------------------------------------------------------
    Γ ⊢ lam T ▸ t :[ c , det ] T ⇒[ e ] T'

  tapp :
    {ts : Tm ^ 2}
    (_ : Γ ⊢ ts ₀ :[ c , e ] T ⇒[ e ] T')
    (_ : Γ ⊢ ts ₁ :[ c , e ] T)
    → -----------------------------------
    Γ ⊢ app ▸ ts :[ c , e ] T'

  tprim :
    {cs : Reg↓ ^ PrimAr ϕ}
    {ts : Tm ^ PrimAr ϕ}
    (_ : PrimTy ϕ ≡ (cs , c'))
    (_ : ∀ i → Γ ⊢ ts i :[ c , e ] treal (cs i))
    → ------------------------------------------
    Γ ⊢ prim ϕ ▸ ts :[ c , e ] treal c'

  treal : Γ ⊢ real r :[ c , det ] treal A↓

  ttup :
    {Ts : Ty ^ n}
    {ts : Tm ^ n}
    (_ : ∀ i → Γ ⊢ ts i :[ c , e ] Ts i)
    → ----------------------------------
    Γ ⊢ tup n ▸ ts :[ c , e ] ttup n Ts

  tproj :
    {Ts : Ty ^ n}
    {t : Tm ^ 1}
    (i : Fin n)
    (_ : Γ ⊢ t ₀ :[ c , e ] ttup n Ts)
    → --------------------------------
    Γ ⊢ proj n i ▸ t :[ c , e ] Ts i

  tif :
    {ts : Tm ^ 3}
    (_ : Γ ⊢ ts ₀ :[ P↓ , e ] treal A↓)
    (_ : Γ ⊢ ts ₁ :[ c , e ] T)
    (_ : Γ ⊢ ts ₂ :[ c , e ] T)
    → ---------------------------------
    Γ ⊢ if ▸ ts :[ c , e ] T

  tdiff :
    {ts : Tm ^ 2}
    {cs : Reg↓ ^ n}
    {ds : Reg↓ ^ m}
    (_ : c' ≡ A↓ ⊎ c' ≡ P↓)
    (_ : Γ ⊢ ts ₀ :[ c , e ] treals n (make c') ⇒[ det ] treals m (make c'))
    (_ : Γ ⊢ ts ₁ :[ c , e ] treals n (make c'))
    → ----------------------------------------------------------------------
    Γ ⊢ diff ▸ ts :[ c , e ] treals n (make c') ⇒[ det ] treals m (make c')

  -- TODO: Fix the typing rule for solve
  tsolve :
    {ts : Tm ^ 3}
    {cs : Reg↓ ^ n}
    {c₀ : Reg↓}
    (_ : Γ ⊢ ts ₀ :[ c₀ , e ] ttup 2 (lookup $ treal c' ∷ treals n cs ∷ []) ⇒[ det ] treals n cs)
    (_ : Γ ⊢ ts ₁ :[ c₀ , e ] ttup 2 λ {₀ → treal c ; ₁ → treals n cs})
    (_ : Γ ⊢ ts ₂ :[ c₀ , e ] treal c')
    → ----------------------------------------------------------------
    Γ ⊢ solve ▸ ts :[ c₀ , e ] ttup 2 λ {₀ → treal c; ₁ → treals n cs}

  tsample : Γ ⊢ sample :[ c , rnd ] treal M↓

  tassume :
    {t : Tm ^ 1}
    (_ : Γ ⊢ t ₀ :[ c , rnd ] tdist T)
    → --------------------------------
    Γ ⊢ assume ▸ t :[ c , rnd ] T

  tweight :
    {t : Tm ^ 1}
    (_ : Γ ⊢ t ₀ :[ M↓ , rnd ] treal A↓)
    → ----------------------------------
    Γ ⊢ weight ▸ t :[ c , rnd ] tunit

  tinfer :
    {t : Tm ^ 1}
    (_ : Γ ⊢ t ₀ :[ M↓ , e ] tunit ⇒[ rnd ] T)
    → ----------------------------------------
    Γ ⊢ infer ▸ t :[ c , e ] tdist T

  tsub :
    (_ : Γ ⊢ t :[ c , e ] T)
    (_ : e ≤ᵉ e')
    (_ : T <: T')
    → ------------------
    Γ ⊢ t :[ c , e' ] T'

  tpromote :
    (_ : Γ ⊢ t :[ c , e ] T)
    (_ : c ≤ᶜ c')
    → ----------------------
    Γ ⊢ t :[ c' , e ] c ⊙ T

  tdemote :
    (_ : Γ ⊢ t :[ c' , e ] c ⊙ T)
    (_ : c ≤ᶜ c')
    → ---------------------------
    Γ ⊢ t :[ c , e ] T
