module Syntax (ℝ : Set) where

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.Support
open import Lib.BindingSignature

open import Function using (_∘_ ; _$_ ; const)
open import Data.Vec.Functional using (map ; fromList)

Coeff : Set
Coeff = ℕ

pattern ca = 0
pattern cb = 1
pattern cc = 2

Eff : Set
Eff = ℕ

pattern det = 0
pattern rnd = 1

-- Types

data Type : Set where
  treal   : Coeff → Type
  _⇒[_]_  : Type → Eff → Type → Type
  ttup    : ∀ {n} → Vector Type n → Type
  tdist   : Type → Type

-- Terms

data Prim : Set where
  padd    : Prim
  pmul    : Prim
  pwiener : ℝ → Prim

PrimAr : Prim → ℕ
PrimAr padd = 2
PrimAr pmul = 2
PrimAr (pwiener _) = 1

data Dist : Set where
  dnormal : Dist
  dbeta   : Dist
  dwiener : Dist

DistAr : Dist → ℕ
DistAr dnormal = 2
DistAr dbeta   = 2
DistAr dwiener = 0

TermSig : Sig
TermSig = mkSig TermOp TermAr
  module _ where
  data TermOp : Set where
    oabs    : Type → TermOp
    oapp    : TermOp
    oprim   : Prim → TermOp
    oreal   : ℝ → TermOp
    otup    : ℕ → TermOp
    oproj   : ℕ → TermOp
    oif     : TermOp
    odiff   : TermOp
    osolve  : TermOp
    odist   : Dist → TermOp
    oassume : TermOp
    oweight : TermOp
    oinfer  : TermOp
    oexpect : TermOp
  TermAr : TermOp → Array ℕ
  length (TermAr (oabs _))  = 1
  length (TermAr oapp)      = 2
  length (TermAr (oprim ϕ)) = PrimAr ϕ
  length (TermAr (oreal _)) = 0
  length (TermAr (otup n))  = n
  length (TermAr (oproj _)) = 1
  length (TermAr oif)       = 3
  length (TermAr odiff)     = 2
  length (TermAr osolve)    = 3
  length (TermAr (odist D)) = DistAr D
  length (TermAr oassume)   = 1
  length (TermAr oweight)   = 1
  length (TermAr oinfer)    = 1
  length (TermAr oexpect)   = 1
  index  (TermAr (oabs _))  = const 1
  index  (TermAr _)         = const 0

Term : Set
Term = Trm TermSig

instance
  lnsTerm = lnsTrm

-- Substitution

-- Bound variable substitution
_≈>_ : ℕ → Term → Term → Term
(n ≈> u) t = Subst.substTrm t ρ
  where
  ρ : ℕ𝔸 → Term
  ρ (ι₁ x) = case (n ≐ x) λ
    { equ     → u
    ; (neq _) → bvar x
    }
  ρ (ι₂ y) = fvar y

-- Free variable substitution
_=>_ : 𝔸 → Term → Term → Term
(a => u) t = Subst.substTrm t ρ
  where
  ρ : ℕ𝔸 → Term
  ρ (ι₁ x) = bvar x
  ρ (ι₂ y) = case (a ≐ y) λ
    { equ     → u
    ; (neq _) → fvar y
    }

-- Syntax shorthands

tup₂ : ∀ {A : Set} → A → A → Vector A 2
tup₂ x y = fromList $ x :: y :: []

tup₃ : ∀ {A : Set} → A → A → A → Vector A 3
tup₃ x y z = fromList $ x :: y :: z :: []

tunit : Type
tunit = ttup {0} λ()

treals : ∀ {n} → Vector Coeff n → Type
treals cs = ttup $ map treal cs

tpair : Type → Type → Type
tpair T₁ T₂ = ttup $ tup₂ T₁ T₂

abs : Type → Term → Term
abs T t = op (oabs T , const t)

app : Term → Term → Term
app t₁ t₂ = op (oapp , tup₂ t₁ t₂)

prim : (ϕ : Prim) → Vector Term (PrimAr ϕ) → Term
prim ϕ ts = op (oprim ϕ , ts)

real : ℝ → Term
real r = op (oreal r , λ ())

tup : ∀ {n} → Vector Term n → Term
tup ts = op (otup _ , ts)

proj : ∀ {n} → Fin n → Term → Term
proj {n} i t = op (oproj n , const t)

if : Term → Term → Term → Term
if t₁ t₂ t₃ = op (oif , tup₃ t₁ t₂ t₃)

diff : Term → Term → Term
diff t₁ t₂ = op (odiff , tup₂ t₁ t₂)

solve : Term → Term → Term → Term
solve t₁ t₂ t₃ = op (osolve , tup₃ t₁ t₂ t₃)

dist : (D : Dist) → Vector Term (DistAr D) → Term
dist D ts = op (odist D , ts)

assume : Term → Term
assume t = op (oassume , const t)

weight : Term → Term
weight t = op (oweight , const t)

expect : Term → Term
expect t = op (oexpect , const t)

infer : Term → Term
infer t = op (oinfer , const t)

unit : Term
unit = tup {0} λ()
