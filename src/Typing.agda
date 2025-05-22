open import Lib.Reals

module Typing (R : Reals₀) where

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

  sreal
    : ∀ {c c′}
    → c′ ≤′ c
    → -------------------
      treal c <: treal c′

  stup
    : ∀ {n Ts Ts′}
    → (∀ i → Ts i <: Ts′ i)
    → -----------------------
      ttup n Ts <: ttup n Ts′

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

  tvar
    : ∀ {x T}
    → -----------------------------
      [ x ∶ T ] ⊢ fvar x :[ det ] T

  tabs
    : ∀ {Γ T₁ T₂ t e}
    → И x ∶ 𝔸 , Γ , x ∶ T₁ ⊢ conc (t ₀) x :[ e ] T₂
    → ---------------------------------------------
      Γ ⊢ abs T₁ ▸ t :[ det ] T₁ ⇒[ e ] T₂

  tapp
    : ∀ {Γ ts e T₁ T₂}
    → Γ ⊢ ts ₀ :[ e ] T₁ ⇒[ e ] T₂
    → Γ ⊢ ts ₁ :[ e ] T₁
    → --------------------
      Γ ⊢ app ▸ ts :[ e ] T₂

  tprim
    : ∀ {ϕ Γ cs c ts e}
    → PrimTy ϕ ≡ (cs , c)
    → Distinct Γ
    → (∀ i → Γ ⊢ ts i :[ e ] treal (cs i))
    → ------------------------------------
      Γ ⊢ prim ϕ ▸ ts :[ e ] treal c

  treal
    : ∀ {r}
    → -----------------------------
      [] ⊢ real r :[ det ] treal N

  ttup
    : ∀ {n Γ Ts ts e}
    → Distinct Γ
    → (∀ i → Γ ⊢ ts i :[ e ] Ts i)
    → -----------------------------
      Γ ⊢ tup n ▸ ts :[ e ] ttup n Ts

  tproj
    : ∀ {n Ts Γ t e} i
    → Γ ⊢ t ₀ :[ e ] ttup n Ts
    → ----------------------------
      Γ ⊢ proj n i ▸ t :[ e ] Ts i

  tif
    : ∀ {Γ ts e T}
    → Γ ⊢ ts ₀ :[ e ] treal P
    → Γ ⊢ ts ₁ :[ e ] T
    → Γ ⊢ ts ₂ :[ e ] T
    → ------------------
      Γ ⊢ if ▸ ts :[ e ] T

  tdiff
    : ∀ {Γ ts n m cs ds e}
    → (∀ i → cs i ≤′ P)
    → Γ ⊢ ts ₀ :[ e ] treals n cs ⇒[ det ] treals m ds
    → Γ ⊢ ts ₁ :[ e ] treals n cs
    → -----------------------------------------------------------
      Γ ⊢ diff ▸ ts :[ e ] treals n (const A) ⇒[ det ] treals m ds

  tsolve
    : ∀ {Γ ts n c cs e}
    → Γ ⊢ ts ₀ :[ e ] ttup 2 (λ {₀ → treal c; ₁ → treals n cs}) ⇒[ det ] treals n cs
    → Γ ⊢ ts ₁ :[ e ] treals n cs
    → Γ ⊢ ts ₂ :[ e ] treal c
    → P ≤′ c
    → ---------------------------------
      Γ ⊢ solve ▸ ts :[ e ] treals n cs

  tdist
    : ∀ {D Γ cs T ts e}
    → DistTy D ≡ (cs , T)
    → Distinct Γ
    → (∀ i → Γ ⊢ ts i :[ e ] treal (cs i))
    → ------------------------------------
      Γ ⊢ dist D ▸ ts :[ e ] tdist T

  tassume
    : ∀ {Γ t T}
    → Γ ⊢ t ₀ :[ rnd ] tdist T
    → -----------------------
      Γ ⊢ assume ▸ t :[ rnd ] T

  tweight
    : ∀ {Γ t}
    → Γ ⊢ t ₀ :[ rnd ] treal N
    → ---------------------------
      Γ ⊢ weight ▸ t :[ rnd ] tunit

  tinfer
    : ∀ {Γ t e T}
    → Γ ⊢ t ₀ :[ e ] tunit ⇒[ rnd ] T
    → N ≤ᴱ Γ
    → -------------------------------
      Γ ⊢ infer ▸ t :[ e ] tdist T

  tweaken
    : ∀ {Γ Γ′ t e T}
    → Γ′ ⊢ t :[ e ] T
    → Γ′ ⊆ Γ
    → Distinct Γ
    → --------------
      Γ ⊢ t :[ e ] T

  tsub
    : ∀ {Γ t e e′ T T′}
    → Γ ⊢ t :[ e ] T
    → e ≤′ e′
    → T <: T′
    → ----------------
      Γ ⊢ t :[ e′ ] T′

  tpromote
    : ∀ {Γ t e c T}
    → Γ ⊢ t :[ e ] T
    → c ≤ᴱ Γ
    → ------------------
      Γ ⊢ t :[ e ] c ⊙ T
