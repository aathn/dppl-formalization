open import DPPL.Regularity

open import Lib.LocallyNameless.BindingSignature
open import Lib.LocallyNameless.Support
open import Lib.Algebra.Reals
open import Lib.Data.Vector
open import Lib.Prelude

open import Order.Base

module DPPL.Syntax (R : Reals₀) where

open Reals R using (ℝ)

-- Types

data Ty : Type where
  treal  : (c : Reg↓) → Ty
  _⇒[_]_ : (T : Ty) (X : Reg⊆) (T' : Ty) → Ty
  ttup   : (n : Nat) (Ts : Ty ^ n) → Ty

open Reg⊆-lat
open Reg≤

_∩ᵗ_ : Reg⊆ → Ty → Ty
X ∩ᵗ treal c       = treal (Close-downward · (X ∩ hom c))
X ∩ᵗ ttup n Ts     = ttup n λ i → X ∩ᵗ Ts i
X ∩ᵗ (T ⇒[ Y ] T') = T ⇒[ X ∩ Y ] T'

_≤ᵗ_ : Ty → Reg⊆ → Type
_≤ᵗ_ (treal c)    X = (y : ∫ₚ c) → ∃[ x ∈ ∫ₚ (X ∩ hom c) ] y .fst ≤ x .fst
_≤ᵗ_ (_ ⇒[ Y ] _) X = Y ⊆ X
_≤ᵗ_ (ttup n Ts)  X = ∀ i → Ts i ≤ᵗ X

_~ᵗ_ : Reg⊆ → Ty → Type
X ~ᵗ treal c      = ⊤
X ~ᵗ (_ ⇒[ Y ] _) = X ~ʳ Y
X ~ᵗ ttup n Ts    = ∀ i → X ~ᵗ Ts i

-- Terms

data Prim : Type where
  padd    : Prim
  psub    : Prim
  pmul    : Prim
  pdiv    : Prim
  psin    : Prim
  pcos    : Prim
  pabs    : Prim
  pwiener : Prim

PrimAr : Prim → Nat
PrimAr padd    = 2
PrimAr psub    = 2
PrimAr pmul    = 2
PrimAr pdiv    = 2
PrimAr psin    = 1
PrimAr pcos    = 1
PrimAr pabs    = 1
PrimAr pwiener = 2

TmSig : Sig
TmSig = mkSig TmOp TmAr
  module _ where
  data TmOp : Type where
    lam      : Ty → TmOp
    app      : TmOp
    prim     : Prim → TmOp
    oreal    : ℝ → TmOp
    tup      : Nat → TmOp
    proj     : (n : Nat) → Fin n → TmOp
    if       : TmOp
    diff     : TmOp
    solve    : TmOp
  TmAr : TmOp → Array Nat
  length (TmAr (lam _))    = 1
  length (TmAr app)        = 2
  length (TmAr (prim ϕ))   = 1
  length (TmAr (oreal _))  = 0
  length (TmAr (tup n))    = n
  length (TmAr (proj _ _)) = 1
  length (TmAr if)         = 3
  length (TmAr diff)       = 3
  length (TmAr solve)      = 3
  index  (TmAr (lam _)) _  = 1
  index  (TmAr _)       _  = 0

Tm : Type
Tm = Trm TmSig

instance
  lnsTm : lns Tm
  lnsTm = lnsTrm

-- Syntax shorthands

pattern ₀ = fin 0
pattern ₁ = fin 1
pattern ₂ = fin 2

infix 25 _▸_
pattern _▸_ x y = op (x , y)

tunit : Ty
tunit = ttup 0 λ()

treals : (n : Nat) → Reg↓ ^ n → Ty
treals n cs = ttup n $ map treal cs

unit : Tm
unit = tup 0 ▸ λ()

real : ℝ → Tm
real r = oreal r ▸ λ ()

pair : ∀ {ℓ} {A : Type ℓ} → A → A → A ^ 2
pair x y = lookup (x ∷ y ∷ []) where open VecSyntax

-- Metavariables

module SyntaxVars where
  variable
    m n  : Nat
    r r' : ℝ
    ϕ    : Prim
    T T' : Ty
    c c' : Reg↓
    X X' : Reg⊆
    t t' : Tm

open SyntaxVars

-- Injectivity lemmas

ttup-inj : ∀ {Ts Ts'} → ttup n Ts ≡ ttup m Ts' → (n , Ts) ≡ (m , Ts')
ttup-inj {n} {Ts = Ts} = ap λ where
  (ttup n Ts) → n , Ts
  _ → n , Ts

real-inj : real r ≡ real r' → r ≡ r'
real-inj {r = r} = ap λ where
  (oreal r ▸ _) → r
  _             → r
