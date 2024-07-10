module Typing (ℝ : Set) where

open import Syntax ℝ

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.AbstractionConcretion hiding (abs)
open import Lib.BindingSignature

open import Function using (_∘_ ; _$_ ; const)
open import Data.List using (map)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_)
open import Data.Nat using (_⊔_)
open import Relation.Binary using (Rel)

TyEnv : Set
TyEnv = List (𝔸 × Type)

pattern [_∶_]   x T = (x , T) :: []
pattern _,_∶_ Γ x T = (x , T) :: Γ

dom : TyEnv → Fset 𝔸
dom [] = Ø
dom (Γ , x ∶ _) = [ x ] ∪ dom Γ

DistinctName : Rel (𝔸 × Type) _
DistinctName (x , _) (x₁ , _) = ¬ x ≡ x₁

open import Data.List.Relation.Unary.AllPairs.Core DistinctName
  using () renaming (AllPairs to Distinct)

_⇒ᵖ_ : ∀ {n} → Vector Coeff n → Type → Vector Coeff n × Type
_⇒ᵖ_ = _,_

PrimTy : (ϕ : Prim) → Vector Coeff (PrimAr ϕ) × Type
PrimTy padd        = const ca ⇒ᵖ treal ca
PrimTy pmul        = const ca ⇒ᵖ treal ca
PrimTy (pwiener r) = const cc ⇒ᵖ treal cc

DistTy : (D : Dist) → Vector Coeff (DistAr D) × Type
DistTy dnormal = const cc ⇒ᵖ treal cc
DistTy dbeta   = const cc ⇒ᵖ treal cc
DistTy dwiener = (λ()) ⇒ᵖ (treal cc ⇒[ det ] treal cc)

_⊙_ : Coeff → Type → Type
c ⊙ (treal c′) = treal (c ⊔ c′)
c ⊙ (ttup Ts)  = ttup $ c ⊙_ ∘ Ts
c ⊙ T          = T

_⊙ᴱ_ : Coeff → TyEnv → TyEnv
c ⊙ᴱ Γ = map (λ (x , T) → x , c ⊙ T) Γ

infix 5 _<:_
data _<:_ : Type → Type → Set where

  sreal
    : ∀ {c c′}
    → c′ ≤ c
    → -------------------
      treal c <: treal c′

  stup
    : ∀ {n Ts Ts′}
    → (∀ (i : Fin n) → Ts i <: Ts′ i)
    → -------------------------------
      ttup Ts <: ttup Ts′

  sarr
    : ∀ {T₁ T₁′ T₂ T₂′ e e′}
    → T₁′ <: T₁ → T₂ <: T₂′ → e ≤ e′
    → -------------------------------
      T₁ ⇒[ e ] T₂ <: T₁′ ⇒[ e′ ] T₂′

  sdist
    : ∀ {T T′}
    → T <: T′
    → -------------------
      tdist T <: tdist T′


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
      Γ ⊢ abs T₁ t :[ det ] T₁ ⇒[ e ] T₂

  tapp
    : ∀ {Γ ts e T₁ T₂}
    → Γ ⊢ ts ₀ :[ e ] T₁ ⇒[ e ] T₂
    → Γ ⊢ ts ₁ :[ e ] T₁
    → --------------------
      Γ ⊢ app ts :[ e ] T₂

  tprim
    : ∀ {ϕ Γ cs T ts e}
    → PrimTy ϕ ≡ cs ⇒ᵖ T
    → (∀ i → Γ ⊢ ts i :[ e ] treal (cs i))
    → ------------------------------------
      Γ ⊢ prim ϕ ts :[ e ] T

  treal

    : ∀ {r}
    → -----------------------------
      [] ⊢ real r :[ det ] treal cc

  ttup
    : ∀ {n Γ Ts ts e}
    → (∀ i → Γ ⊢ ts i :[ e ] Ts i)
    → -----------------------------
      Γ ⊢ tup {n} ts :[ e ] ttup Ts

  tproj
    : ∀ {n Ts Γ t e} i
    → Γ ⊢ t ₀ :[ e ] ttup Ts
    → ----------------------------
      Γ ⊢ proj {n} i t :[ e ] Ts i

  tif
    : ∀ {Γ ts e T}
    → Γ ⊢ ts ₀ :[ e ] treal cb
    → Γ ⊢ ts ₁ :[ e ] T
    → Γ ⊢ ts ₂ :[ e ] T
    → ------------------
      Γ ⊢ if ts :[ e ] T

  tdiff
    : ∀ {Γ ts n m cs ds e}
    → (∀ i → cs i ≤ cb)
    → Γ ⊢ ts ₀ :[ e ] treals {n} cs ⇒[ det ] treals {m} ds
    → Γ ⊢ ts ₁ :[ e ] treals cs
    → -----------------------------------------------------------
      Γ ⊢ diff ts :[ e ] treals {n} (const ca) ⇒[ det ] treals ds

  tsolve
    : ∀ {Γ ts n c cs e}
    → Γ ⊢ ts ₀ :[ e ] ttup {2} (λ {₀ → treal c; ₁ → treals {n} cs}) ⇒[ det ] treals cs
    → Γ ⊢ ts ₁ :[ e ] treals cs
    → Γ ⊢ ts ₂ :[ e ] treal c
    → -----------------------------
      Γ ⊢ solve ts :[ e ] treals cs

  tdist
    : ∀ {D Γ cs T ts e}
    → DistTy D ≡ cs ⇒ᵖ T
    → (∀ i → Γ ⊢ ts i :[ e ] treal (cs i))
    → ------------------------------------
      Γ ⊢ dist D ts :[ e ] tdist T

  tassume
    : ∀ {Γ t T}
    → Γ ⊢ t ₀ :[ rnd ] tdist T
    → -----------------------
      Γ ⊢ assume t :[ rnd ] T

  tweight
    : ∀ {Γ t}
    → Γ ⊢ t ₀ :[ rnd ] treal cc
    → ---------------------------
      Γ ⊢ weight t :[ rnd ] tunit

  texpect
    : ∀ {Γ t e}
    → Γ ⊢ t ₀ :[ e ] tdist (treal cc)
    → -----------------------------
      Γ ⊢ expect t :[ e ] treal cc

  tinfer
    : ∀ {Γ t e T}
    → Γ ⊢ t ₀ :[ e ] tunit ⇒[ rnd ] T
    → -------------------------------
      Γ ⊢ infer t :[ e ] tdist T

  tweaken
    : ∀ {Γ Γ′ t e T}
    → Γ ⊢ t :[ e ] T
    → Γ ⊆ Γ′
    → Distinct Γ′
    → ---------------
      Γ′ ⊢ t :[ e ] T

  tsub
    : ∀ {Γ t e e′ T T′}
    → Γ ⊢ t :[ e ] T
    → e ≤ e′
    → T <: T′
    → ----------------
      Γ ⊢ t :[ e′ ] T′

  tpromote
    : ∀ {Γ Γ′ t e c T}
    → Γ ⊢ t :[ e ] T
    → Γ′ ≡ c ⊙ᴱ Γ
    → -------------------
      Γ′ ⊢ t :[ e ] c ⊙ T
