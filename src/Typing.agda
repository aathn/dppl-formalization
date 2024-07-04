module Typing (ℝ : Set) where

open import Syntax ℝ

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.AbstractionConcretion hiding (abs)
open import Lib.BindingSignature

open import Function using (const ; _∘_)
open import Data.List using (map)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_)
open import Data.Nat using (_⊔_)

TyEnv : Set
TyEnv = List (𝔸 × Type)

pattern [_∶_]   x T = (x , T) :: []
pattern _,_∶_ Γ x T = (x , T) :: Γ

record PrimType : Set where
  constructor _⇒ᵖ_
  field
    dom   : Array Type
    codom : Type

open PrimType

PrTy : Prim → PrimType
length (dom (PrTy padd))   = 2
index  (dom (PrTy padd)) i = treal ca
codom       (PrTy padd)    = treal ca
length (dom (PrTy pmul))   = 2
index  (dom (PrTy pmul)) i = treal ca
codom       (PrTy pmul)    = treal ca
length (dom (PrTy (pwiener r)))   = 1
index  (dom (PrTy (pwiener r))) i = treal cc
codom       (PrTy (pwiener r))    = treal cc

DiTy : Dist → PrimType
length (dom (DiTy dnormal))   = 2
index  (dom (DiTy dnormal)) i = treal cc
codom       (DiTy dnormal)    = treal cc
length (dom (DiTy dbeta))     = 2
index  (dom (DiTy dbeta))   i = treal cc
codom       (DiTy dbeta)      = treal cc
length (dom (DiTy dwiener))   = 0
codom       (DiTy dwiener)    = treal cc ⇒[ det ] treal cc

_⊙_ : Coeff → Type → Type
c ⊙ (treal c′) = treal (c ⊔ c′)
c ⊙ (ttup Ts)  = ttup (mkArray _ (c ⊙_ ∘ index Ts))
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
    → -------------------------------------------
      ttup (mkArray _ Ts) <: ttup (mkArray _ Ts′)

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


infix 4 _⊢_∶[_]_
data _⊢_∶[_]_ : TyEnv → Term → Eff → Type → Set where

  tvar
    : ∀ {x T}
    → -----------------------------
      [ x ∶ T ] ⊢ fvar x ∶[ det ] T

  tabs
    : ∀ {Γ T₁ T₂ t e}
    → И x ∶ 𝔸 , Γ , x ∶ T₁ ⊢ conc t x ∶[ e ] T₂
    → -----------------------------------------
      Γ ⊢ abs T₁ t ∶[ det ] T₁ ⇒[ e ] T₂

  tapp
    : ∀ {Γ t₁ t₂ e T₁ T₂}
    → Γ ⊢ t₁ ∶[ e ] T₁ ⇒[ e ] T₂
    → Γ ⊢ t₂ ∶[ e ] T₂
    → --------------------------
      Γ ⊢ app t₁ t₂ ∶[ e ] T₂

  tprim
    : ∀ {ϕ Γ Ts T ts e}
    → PrTy ϕ ≡ Ts ⇒ᵖ T
    → (∀ i → Γ ⊢ ts i ∶[ e ] index Ts i)
    → ----------------------------------
      Γ ⊢ prim ϕ ts ∶[ e ] T

  treal
    : ∀ {Γ r}
    → ----------------------------
      Γ ⊢ real r ∶[ det ] treal cc

  ttup
    : ∀ {Γ Ts ts e}
    → (∀ i → Γ ⊢ ts i ∶[ e ] index Ts i)
    → ----------------------------------
      Γ ⊢ tup ts ∶[ e ] ttup Ts

  tproj
    : ∀ {Ts Γ i t e}
    → Γ ⊢ t ∶[ e ] ttup Ts
    → ------------------------------
      Γ ⊢ proj i t ∶[ e ] index Ts i

  tif
    : ∀ {Γ t₁ t₂ t₃ e T}
    → Γ ⊢ t₁ ∶[ e ] treal cb
    → Γ ⊢ t₂ ∶[ e ] T
    → Γ ⊢ t₃ ∶[ e ] T
    → ------------------------
      Γ ⊢ if t₁ t₂ t₃ ∶[ e ] T

  tdiff
    : ∀ {Γ t₁ t₂ n m cs ds e}
    → (∀ i → cs i ≤ cb)
    → Γ ⊢ t₁ ∶[ e ] treals {n} cs ⇒[ det ] treals {m} ds
    → Γ ⊢ t₂ ∶[ e ] treals cs
    → --------------------------------------------------------------
      Γ ⊢ diff t₁ t₂ ∶[ e ] treals {n} (const ca) ⇒[ det ] treals ds

  tsolve
    : ∀ {Γ t₁ t₂ t₃ n c cs e}
    → Γ ⊢ t₁ ∶[ e ] tpair (treal c) (treals {n} cs) ⇒[ det ] treals cs
    → Γ ⊢ t₂ ∶[ e ] treals cs
    → Γ ⊢ t₃ ∶[ e ] treal c
    → ----------------------------------------------------------------
      Γ ⊢ solve t₁ t₂ t₃ ∶[ e ] treals cs

  tdist
    : ∀ {D Γ Ts T ts e}
    → DiTy D ≡ Ts ⇒ᵖ T
    → (∀ i → Γ ⊢ ts i ∶[ e ] index Ts i)
    → ----------------------------------
      Γ ⊢ dist D ts ∶[ e ] tdist T

  tassume
    : ∀ {Γ t e T}
    → Γ ⊢ t ∶[ e ] tdist T
    → -----------------------
      Γ ⊢ assume t ∶[ rnd ] T

  tweight
    : ∀ {Γ t e}
    → Γ ⊢ t ∶[ e ] treal cc
    → ---------------------------
      Γ ⊢ weight t ∶[ rnd ] tunit

  texpect
    : ∀ {Γ t e}
    → Γ ⊢ t ∶[ e ] tdist (treal cc)
    → -----------------------------
      Γ ⊢ expect t ∶[ e ] treal cc

  tinfer
    : ∀ {Γ t e T}
    → Γ ⊢ t ∶[ e ] tunit ⇒[ rnd ] T
    → -----------------------------
      Γ ⊢ infer t ∶[ e ] tdist T

  tweaken
    : ∀ {Γ Γ′ t e T}
    → Γ ⊢ t ∶[ e ] T
    → Γ ⊆ Γ′ -- → okEnv Γ′
    → ---------------
      Γ′ ⊢ t ∶[ e ] T

  tsub
    : ∀ {Γ t e e′ T T′}
    → Γ ⊢ t ∶[ e ] T
    → e ≤ e′ → T <: T′
    → ----------------
      Γ ⊢ t ∶[ e′ ] T′

  tpromote
    : ∀ {Γ t e c T}
    → Γ ⊢ t ∶[ e ] T
    → -----------------------
      c ⊙ᴱ Γ ⊢ t ∶[ e ] c ⊙ T
