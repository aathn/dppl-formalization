open import Data.Power using (singleton)

open import DPPL.Regularity

open import Lib.LocallyNameless.AbstractionConcretion
open import Lib.LocallyNameless.BindingSignature
open import Lib.LocallyNameless.Unfinite
open import Lib.Algebra.Reals
open import Lib.Data.Vector
open import Lib.Syntax.Env
open import Lib.Prelude

open import Order.Base

import DPPL.Syntax as Syntax

module DPPL.Typing (R : Reals₀) where

open VectorSyntax using () renaming (_∷_ to _∷ᵛ_)
open VecSyntax
open Reg⊆-lat
open Syntax R
open Reg≤

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
PrimTy psub    = make A↓ , A↓
PrimTy pmul    = make A↓ , A↓
PrimTy pdiv    = lookup (A↓ ∷ P↓ ∷ []) , P↓
PrimTy psin    = make A↓ , A↓
PrimTy pcos    = make A↓ , A↓
PrimTy pabs    = make PC↓ , PC↓
PrimTy pwiener = lookup (Ø↓ ∷ C↓ ∷ []) , C↓

infix 5 _<:_
data _<:_ : Ty → Ty → Type where

  sreal :
    (H⊆ : c ⊆ c')
    → -----------------
    treal c <: treal c'

  stup :
    {Ts Ts' : Ty ^ n}
    (H<: : ∀ i → Ts i <: Ts' i)
    → -------------------------
    ttup n Ts <: ttup n Ts'

  sarr :
    {T₁ T₁' T₂ T₂' : Ty}
    (H<:₁ : T₁' <: T₁)
    (H⊆ : X ⊆ X')
    (H<:₂ : T₂ <: T₂')
    → -----------------------------
    T₁ ⇒[ X ] T₂ <: T₁' ⇒[ X' ] T₂'

_≤ᵉ_ : TyEnv → Reg⊆ → Type
Γ ≤ᵉ X = ∀ {a T} → a ∶ T ∈ Γ → T ≤ᵗ X

infix 4 _⊢_∶_
data _⊢_∶_ : TyEnv → Tm → Ty → Type where

  tsub :
    (Hty : Γ ⊢ t ∶ T)
    (H<: : T <: T')
    → ---------------
    Γ ⊢ t ∶ T'

  tpromote :
    (Hty : Γ ⊢ t ∶ T)
    (H≤ : Γ ≤ᵉ X)
    (H~ : X ~ᵗ T)
    (H⊆ : Γ ⊆ Γ')
    → ---------------
    Γ' ⊢ t ∶ X ∩ᵗ T

  tvar :
    (H∈ : a ∶ T ∈ Γ)
    → --------------
    Γ ⊢ fvar a ∶ T

  tlam :
    {t : Tm ^ 1}
    (Hlam : И[ a ∈ 𝔸 ] (Γ , a ∶ T) ⊢ conc (t ₀) a ∶ T')
    → -------------------------------------------------
    Γ ⊢ lam T ▸ t ∶ T ⇒[ top ] T'

  tapp :
    {ts : Tm ^ 2}
    (Hty₁ : Γ ⊢ ts ₀ ∶ T ⇒[ top ] T')
    (Hty₂ : Γ ⊢ ts ₁ ∶ T)
    → ------------------------------------
    Γ ⊢ app ▸ ts ∶ T'

  tprim :
    {cs : Reg↓ ^ PrimAr ϕ}
    {t : Tm ^ 1}
    (Hϕ : PrimTy ϕ ≡ (cs , c))
    (Htys : Γ ⊢ t ₀ ∶ treals _ cs)
    → ----------------------------
    Γ ⊢ prim ϕ ▸ t ∶ treal c

  treal :
    {t : Tm ^ 0}
    → -----------------------
    Γ ⊢ oreal r ▸ t ∶ treal c

  ttup :
    {Ts : Ty ^ n}
    {ts : Tm ^ n}
    (Htys : ∀ i → Γ ⊢ ts i ∶ Ts i)
    → ----------------------------
    Γ ⊢ tup n ▸ ts ∶ ttup n Ts

  tproj :
    {Ts : Ty ^ n}
    {t : Tm ^ 1}
    (i : Fin n)
    (Hty : Γ ⊢ t ₀ ∶ ttup n Ts)
    → -------------------------
    Γ ⊢ proj n i ▸ t ∶ Ts i

  tif :
    {cs : Reg↓ ^ n}
    {ts : Tm ^ 3}
    (Hty : Γ ⊢ ts ₀ ∶ treal P↓)
    (Hty₁ : Γ ⊢ ts ₁ ∶ treals n cs)
    (Hty₂ : Γ ⊢ ts ₂ ∶ treals n cs)
    (H≤ : ∀ i → P↓ ⊆ cs i)
    → -----------------------------
    Γ ⊢ if ▸ ts ∶ treals n cs

  tdiff :
    {ts : Tm ^ 3}
    (Hty : Γ ⊢ ts ₀ ∶ treals m (make c) ⇒[ singleton P ] treals n (make c))
    (Hty₁ : Γ ⊢ ts ₁ ∶ treals m (make c))
    (Hty₂ : Γ ⊢ ts ₂ ∶ treals m (make A↓))
    (Hc : c ≡ A↓ ⊎ c ≡ P↓)
    → ---------------------------------------------------------------------
    Γ ⊢ diff ▸ ts ∶ treals n (make A↓)

  tsolve :
    {ts : Tm ^ 3}
    (Hty : Γ ⊢ ts ₀ ∶ treals (1 + n) (c ∷ᵛ make A↓) ⇒[ singleton C ] treals n (make A↓))
    (Hty₁ : Γ ⊢ ts ₁ ∶ treals (1 + n) (c ∷ᵛ make A↓))
    (Hty₂ : Γ ⊢ ts ₂ ∶ treal (c Reg↓-lat.∩ PC↓))
    (Hc : c ≡ A↓ ⊎ c ≡ C↓)
    → ----------------------------------------------------------------------------------
    Γ ⊢ solve ▸ ts ∶ treals (1 + n) (make A↓)
