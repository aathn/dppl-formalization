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
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴱ_)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Unary.All using (All)

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

_≤ᴱ_ : Coeff → TyEnv → Set
c ≤ᴱ Γ = All (c ≤ᶜ_ ∘ π₂) Γ


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
    → T₁′ <: T₁ → T₂ <: T₂′ → e ≤′ e′
    → -------------------------------
      T₁ ⇒[ e ] T₂ <: T₁′ ⇒[ e′ ] T₂′

  sdist
    : ∀ {T T′}
    → T <: T′
    → -------------------
      tdist T <: tdist T′


_<:ᴱ_ : TyEnv → TyEnv → Set
_<:ᴱ_ = Pointwise (λ (x₁ , T₁) (x₂ , T₂) → x₁ ≡ x₂ × T₁ <: T₂)


infix 4 _⊢_:[_]_
data _⊢_:[_]_ : TyEnv → Term → Eff → Type → Set where

  tvar :
    {x : 𝔸}
    {T : Type}
    {Γ : TyEnv}
    (_ : (x , T) ∈ᴱ Γ)
    (_ : Distinct Γ)
    → -------------------
    Γ ⊢ fvar x :[ det ] T

  tabs :
    {Γ : TyEnv}
    {T₁ T₂ : Type}
    {t : Vector Term 1}
    {e : Eff}
    (_ : И x ∶ 𝔸 , Γ , x ∶ T₁ ⊢ conc (t ₀) x :[ e ] T₂)
    → -------------------------------------------------
    Γ ⊢ abs T₁ t :[ det ] T₁ ⇒[ e ] T₂

  tapp :
    {Γ : TyEnv}
    {ts : Vector Term 2}
    {e : Eff}
    {T₁ T₂ : Type}
    (_ : Γ ⊢ ts ₀ :[ e ] T₁ ⇒[ e ] T₂)
    (_ : Γ ⊢ ts ₁ :[ e ] T₁)
    → --------------------------------
    Γ ⊢ app ts :[ e ] T₂

  tprim :
    {ϕ : Prim}
    {Γ : TyEnv}
    {cs : Vector Coeff (PrimAr ϕ)}
    {c : Coeff}
    {ts : Vector Term (PrimAr ϕ)}
    {e : Eff}
    (_ : PrimTy ϕ ≡ (cs , c))
    (_ : Distinct Γ)
    (_ : ∀ i → Γ ⊢ ts i :[ e ] treal (cs i))
    → --------------------------------------
    Γ ⊢ prim ϕ ts :[ e ] treal c

  treal :
    {Γ : TyEnv}
    {r : ℝ}
    (_ : Distinct Γ)
    → -------------------------
    Γ ⊢ real r :[ det ] treal N

  ttup :
    {n : ℕ}
    {Γ : TyEnv}
    {Ts : Vector Type n}
    {ts : Vector Term n}
    {e : Eff}
    (_ : Distinct Γ)
    (_ : ∀ i → Γ ⊢ ts i :[ e ] Ts i)
    → ------------------------------
    Γ ⊢ tup ts :[ e ] ttup Ts

  tproj :
    {n : ℕ}
    {Ts : Vector Type n}
    {Γ : TyEnv}
    {t : Vector Term 1}
    {e : Eff}
    (i : Fin n)
    (_ : Γ ⊢ t ₀ :[ e ] ttup Ts)
    → --------------------------
    Γ ⊢ proj i t :[ e ] Ts i

  tif :
    {Γ : TyEnv}
    {ts : Vector Term 3}
    {e : Eff}
    {T : Type}
    (_ : Γ ⊢ ts ₀ :[ e ] treal P)
    (_ : Γ ⊢ ts ₁ :[ e ] T)
    (_ : Γ ⊢ ts ₂ :[ e ] T)
    → ---------------------------
    Γ ⊢ if ts :[ e ] T

  tdiff :
    {Γ : TyEnv}
    {ts : Vector Term 2}
    {n m : ℕ}
    {cs : Vector Coeff n}
    {ds : Vector Coeff m}
    {e : Eff}
    (_ : ∀ i → cs i ≤′ P)
    (_ : Γ ⊢ ts ₀ :[ e ] treals cs ⇒[ det ] treals ds)
    (_ : Γ ⊢ ts ₁ :[ e ] treals cs)
    → --------------------------------------------------------
    Γ ⊢ diff ts :[ e ] treals {n} (const A) ⇒[ det ] treals ds

  tsolve :
    {Γ : TyEnv}
    {ts : Vector Term 3}
    {n : ℕ}
    {c : Coeff}
    {cs : Vector Coeff n}
    {e : Eff}
    (_ : Γ ⊢ ts ₀ :[ e ] ttup {2} (λ {₀ → treal c; ₁ → treals cs}) ⇒[ det ] treals cs)
    (_ : Γ ⊢ ts ₁ :[ e ] treals cs)
    (_ : Γ ⊢ ts ₂ :[ e ] treal P)
    → --------------------------------------------------------------------------------
    Γ ⊢ solve ts :[ e ] treals cs

  tdist :
    {D : Dist}
    {Γ : TyEnv}
    {cs : Vector Coeff (DistAr D)}
    {T : Type}
    {ts : Vector Term (DistAr D)}
    {e : Eff}
    (_ : DistTy D ≡ (cs , T))
    (_ : Distinct Γ)
    (_ : (∀ i → Γ ⊢ ts i :[ e ] treal (cs i)))
    → ----------------------------------------
    Γ ⊢ dist D ts :[ e ] tdist T

  tassume :
    {Γ : TyEnv}
    {t : Vector Term 1}
    {T : Type}
    (_ : Γ ⊢ t ₀ :[ rnd ] tdist T)
    → ----------------------------
    Γ ⊢ assume t :[ rnd ] T

  tweight :
    {Γ : TyEnv}
    {t : Vector Term 1}
    (_ : Γ ⊢ t ₀ :[ rnd ] treal N)
    → ----------------------------
    Γ ⊢ weight t :[ rnd ] tunit

  texpect :
    {Γ : TyEnv}
    {t : Vector Term 1}
    {e : Eff}
    (_ : Γ ⊢ t ₀ :[ e ] tdist (treal N))
    → ----------------------------------
    Γ ⊢ expect t :[ e ] treal N

  tinfer :
    {Γ : TyEnv}
    {t : Vector Term 1}
    {e : Eff}
    {T : Type}
    (_ : Γ ⊢ t ₀ :[ e ] tunit ⇒[ rnd ] T)
    → -----------------------------------
    Γ ⊢ infer t :[ e ] tdist T

  tsub :
    {Γ : TyEnv}
    {t : Term}
    {e e′ : Eff}
    {T T′ : Type}
    (_ : Γ ⊢ t :[ e ] T)
    (_ : e ≤′ e′)
    (_ : T <: T′)
    → ------------------
    Γ ⊢ t :[ e′ ] T′

  tpromote :
    {Γ Γ′ : TyEnv}
    {t : Term}
    {e : Eff}
    {c : Coeff}
    {T : Type}
    (_ : Γ′ ⊢ t :[ e ] T)
    (_ : c ≤ᴱ Γ′)
    (_ : Γ′ ⊆ Γ)
    (_ : Distinct Γ)
    → -------------------
    Γ ⊢ t :[ e ] c ⊙ T
