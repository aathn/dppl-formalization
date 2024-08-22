open import Lib.Reals

module Typing (R : Reals₀) where

open Reals R

open import Syntax R

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.AbstractionConcretion
open import Lib.BindingSignature

open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴱ_)

TyEnv : Set
TyEnv = List (𝔸 × Type)

infixl 5 _,_∶_
pattern [_∶_]   x T = (x , T) ∷ []
pattern _,_∶_ Γ x T = (x , T) ∷ Γ

dom : TyEnv → Fset 𝔸
dom [] = Ø
dom (Γ , x ∶ _) = [ x ] ∪ dom Γ

data Distinct : TyEnv → Set where
  []  : Distinct []
  _∷_ : ∀ {x T Γ} → x ∉ dom Γ → Distinct Γ → Distinct (Γ , x ∶ T)

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
c ⊙ (ttup Ts)  = ttup $ c ⊙_ ∘ Ts
c ⊙ T          = T

_≤ᶜ_ : Coeff → Type → Set
c ≤ᶜ treal d = c ≤′ d
c ≤ᶜ ttup Ts = ∀ i → c ≤ᶜ Ts i
c ≤ᶜ T = 𝟙


infix 5 _<:_
data _<:_ : Type → Type → Set where

  sreal
    : ∀ {c c′}
    → c′ ≤′ c
    → -------------------
      treal c <: treal c′

  stup
    : ∀ {n Ts Ts′}
    → (∀ i → Ts i <: Ts′ i)
    → -----------------------
      ttup {n} Ts <: ttup Ts′

  sarr
    : ∀ {T₁ T₁′ T₂ T₂′ e e′}
    → T₁′ <: T₁ → e ≤′ e′ → T₂ <: T₂′
    → -------------------------------
      T₁ ⇒[ e ] T₂ <: T₁′ ⇒[ e′ ] T₂′

  sdist
    : ∀ {T T′}
    → T <: T′
    → -------------------
      tdist T <: tdist T′

infix 4 _⊢[_]_:[_]_
data _⊢[_]_:[_]_ : TyEnv → Coeff → Term → Eff → Type → Set where

  tvar :
    {x : 𝔸}
    {T : Type}
    {Γ : TyEnv}
    {c : Coeff}
    (_ : (x , T) ∈ᴱ Γ)
    (_ : c ≤ᶜ T)
    (_ : Distinct Γ)
    → ------------------------
    Γ ⊢[ c ] fvar x :[ det ] T

  tlam :
    {Γ : TyEnv}
    {c : Coeff}
    {T₁ T₂ : Type}
    {t : Vector Term 1}
    {e : Eff}
    (_ : И x ∶ 𝔸 , Γ , x ∶ T₁ ⊢[ c ] conc (t ₀) x :[ e ] T₂)
    → ------------------------------------------------------
    Γ ⊢[ c ] lam T₁ t :[ det ] T₁ ⇒[ e ] T₂

  tapp :
    {Γ : TyEnv}
    {c : Coeff}
    {ts : Vector Term 2}
    {e : Eff}
    {T₁ T₂ : Type}
    (_ : Γ ⊢[ c ] ts ₀ :[ e ] T₁ ⇒[ e ] T₂)
    (_ : Γ ⊢[ c ] ts ₁ :[ e ] T₁)
    → -------------------------------------
    Γ ⊢[ c ] app ts :[ e ] T₂

  tprim :
    {ϕ : Prim}
    {Γ : TyEnv}
    {d : Coeff}
    {cs : Vector Coeff (PrimAr ϕ)}
    {c : Coeff}
    {ts : Vector Term (PrimAr ϕ)}
    {e : Eff}
    (_ : PrimTy ϕ ≡ (cs , c))
    (_ : Distinct Γ)
    (_ : ∀ i → Γ ⊢[ d ] ts i :[ e ] treal (cs i))
    → -------------------------------------------
    Γ ⊢[ d ] prim ϕ ts :[ e ] treal c

  treal :
    {Γ : TyEnv}
    {r : ℝ}
    (_ : Distinct Γ)
    → ------------------------------
    Γ ⊢[ N ] real r :[ det ] treal N

  ttup :
    {n : ℕ}
    {Γ : TyEnv}
    {c : Coeff}
    {Ts : Vector Type n}
    {ts : Vector Term n}
    {e : Eff}
    (_ : Distinct Γ)
    (_ : ∀ i → Γ ⊢[ c ] ts i :[ e ] Ts i)
    → -----------------------------------
    Γ ⊢[ c ] tup ts :[ e ] ttup Ts

  tproj :
    {n : ℕ}
    {Ts : Vector Type n}
    {Γ : TyEnv}
    {c : Coeff}
    {t : Vector Term 1}
    {e : Eff}
    (i : Fin n)
    (_ : Γ ⊢[ c ] t ₀ :[ e ] ttup Ts)
    → -------------------------------
    Γ ⊢[ c ] proj i t :[ e ] Ts i

  tif :
    {Γ : TyEnv}
    {c : Coeff}
    {ts : Vector Term 3}
    {e : Eff}
    {T : Type}
    (_ : Γ ⊢[ c ] ts ₀ :[ e ] treal P)
    (_ : Γ ⊢[ c ] ts ₁ :[ e ] T)
    (_ : Γ ⊢[ c ] ts ₂ :[ e ] T)
    → --------------------------------
    Γ ⊢[ c ] if ts :[ e ] T

  tdiff :
    {Γ : TyEnv}
    {c : Coeff}
    {ts : Vector Term 2}
    {n m : ℕ}
    {cs : Vector Coeff n}
    {ds : Vector Coeff m}
    {e : Eff}
    (_ : ∀ i → cs i ≤′ P)
    (_ : Γ ⊢[ c ] ts ₀ :[ e ] treals cs ⇒[ det ] treals ds)
    (_ : Γ ⊢[ c ] ts ₁ :[ e ] treals cs)
    → -------------------------------------------------------------
    Γ ⊢[ c ] diff ts :[ e ] treals {n} (const A) ⇒[ det ] treals ds

  tsolve :
    {Γ : TyEnv}
    {ts : Vector Term 3}
    {n : ℕ}
    {c d : Coeff}
    {cs : Vector Coeff n}
    {e : Eff}
    (_ : Γ ⊢[ d ] ts ₀ :[ e ] ttup {2} (λ {₀ → treal c; ₁ → treals cs}) ⇒[ det ] treals cs)
    (_ : Γ ⊢[ d ] ts ₁ :[ e ] treals cs)
    (_ : Γ ⊢[ d ] ts ₂ :[ e ] treal P)
    → -------------------------------------------------------------------------------------
    Γ ⊢[ d ] solve ts :[ e ] treals cs

  tdist :
    {D : Dist}
    {Γ : TyEnv}
    {c : Coeff}
    {cs : Vector Coeff (DistAr D)}
    {T : Type}
    {ts : Vector Term (DistAr D)}
    {e : Eff}
    (_ : DistTy D ≡ (cs , T))
    (_ : Distinct Γ)
    (_ : (∀ i → Γ ⊢[ c ] ts i :[ e ] treal (cs i)))
    → ---------------------------------------------
    Γ ⊢[ c ] dist D ts :[ e ] tdist T

  tassume :
    {Γ : TyEnv}
    {c : Coeff}
    {t : Vector Term 1}
    {T : Type}
    (_ : Γ ⊢[ c ] t ₀ :[ rnd ] tdist T)
    → ---------------------------------
    Γ ⊢[ c ] assume t :[ rnd ] T

  tweight :
    {Γ : TyEnv}
    {c : Coeff}
    {t : Vector Term 1}
    (_ : Γ ⊢[ c ] t ₀ :[ rnd ] treal N)
    → ---------------------------------
    Γ ⊢[ c ] weight t :[ rnd ] tunit

  texpect :
    {Γ : TyEnv}
    {c : Coeff}
    {t : Vector Term 1}
    {e : Eff}
    (_ : Γ ⊢[ c ] t ₀ :[ e ] tdist (treal N))
    → ---------------------------------------
    Γ ⊢[ c ] expect t :[ e ] treal N

  tinfer :
    {Γ : TyEnv}
    {c : Coeff}
    {t : Vector Term 1}
    {e : Eff}
    {T : Type}
    (_ : Γ ⊢[ c ] t ₀ :[ e ] tunit ⇒[ rnd ] T)
    → ----------------------------------------
    Γ ⊢[ c ] infer t :[ e ] tdist T

  tsub :
    {Γ : TyEnv}
    {c c′ : Coeff}
    {t : Term}
    {e e′ : Eff}
    {T : Type}
    (_ : Γ ⊢[ c ] t :[ e ] T)
    (_ : c′ ≤′ c)
    (_ : e ≤′ e′)
    → -----------------------
    Γ ⊢[ c′ ] t :[ e′ ] T

  tpromote :
    {Γ : TyEnv}
    {t : Term}
    {e : Eff}
    {c c′ d : Coeff}
    {T : Type}
    (_ : Γ ⊢[ d ] t :[ e ] T)
    (_ : d ≡ c′ ⊔′ c)
    → -----------------------
    Γ ⊢[ c′ ] t :[ e ] c ⊙ T

  tdemote :
    {Γ : TyEnv}
    {t : Term}
    {e : Eff}
    {c c′ d : Coeff}
    {T : Type}
    (_ : Γ ⊢[ c′ ] t :[ e ] c ⊙ T)
    (_ : d ≡ c′ ⊔′ c)
    → ----------------------------
    Γ ⊢[ d ] t :[ e ] T
