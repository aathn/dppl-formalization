module Syntax (ℝ : Set) where

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.Support
open import Lib.BindingSignature

open import Function using (_∘_ ; const)

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
  ttup    : Array Type → Type
  tdist   : Type → Type

-- Terms

data Prim : Set where
  padd    : Prim
  pmul    : Prim
  pwiener : ℝ → Prim

data Dist : Set where
  dnormal : Dist
  dbeta   : Dist
  dwiener : Dist

TermSig : Sig
TermSig = mkSig TermOp TermAr
  module _ where
  data TermOp : Set where
    oabs    : Type → TermOp
    oapp    : TermOp
    oprim   : ℕ → Prim → TermOp
    oreal   : ℝ → TermOp
    otup    : ℕ → TermOp
    oproj   : ℕ → TermOp
    oif     : TermOp
    odiff   : TermOp
    osolve  : TermOp
    odist   : ℕ → Dist → TermOp
    oassume : TermOp
    oweight : TermOp
    oinfer  : TermOp
    oexpect : TermOp
  TermAr : TermOp → Array ℕ
  length (TermAr (oabs _))      = 1
  length (TermAr oapp)          = 2
  length (TermAr (oprim n _))   = n
  length (TermAr (oreal _))     = 0
  length (TermAr (otup n))      = n
  length (TermAr (oproj _))     = 1
  length (TermAr oif)           = 3
  length (TermAr odiff)         = 2
  length (TermAr osolve)        = 3
  length (TermAr (odist n _))   = n
  length (TermAr oassume)       = 1
  length (TermAr oweight)       = 1
  length (TermAr oinfer)        = 1
  length (TermAr oexpect)       = 1
  index  (TermAr (oabs _))    i = 1
  index  (TermAr oapp)        i = 0
  index  (TermAr (oprim _ _)) i = 0
  index  (TermAr (otup _))    i = 0
  index  (TermAr (oproj _))   i = 0
  index  (TermAr oif)         i = 0
  index  (TermAr odiff)       i = 0
  index  (TermAr osolve)      i = 0
  index  (TermAr (odist _ _)) i = 0
  index  (TermAr oassume)     i = 0
  index  (TermAr oweight)     i = 0
  index  (TermAr oinfer)      i = 0
  index  (TermAr oexpect)     i = 0

Term : Set
Term = Trm TermSig

instance
  lnsTerm = lnsTrm

-- Substitution

_≈>_ : 𝔸 → Term → Term → Term
(a ≈> u) t = Subst.substTrm t ρ
  where
  ρ : ℕ𝔸 → Term
  ρ (ι₁ x) = bvar x
  ρ (ι₂ y) = case (a ≐ y) λ
    { equ     → u
    ; (neq _) → fvar y
    }

-- Syntax shorthands

tup₂ : ∀ {A : Set} → A → A → Fin 2 → A
tup₂ x y zero        = x
tup₂ x y (succ zero) = y

tup₃ : ∀ {A : Set} → A → A → A → Fin 3 → A
tup₃ x y z zero               = x
tup₃ x y z (succ zero)        = y
tup₃ x y z (succ (succ zero)) = z

tunit : Type
tunit = ttup (mkArray 0 λ())

treals : ∀ {n} → (Fin n → Coeff) → Type
treals cs = ttup (mkArray _ (treal ∘ cs))

tpair : Type → Type → Type
tpair T₁ T₂ = ttup (mkArray _ (tup₂ T₁ T₂))

abs : Type → Term → Term
abs T t = op (oabs T , const t)

app : Term → Term → Term
app t₁ t₂ = op (oapp , tup₂ t₁ t₂)

prim : ∀ {n} → Prim → (Fin n → Term) → Term
prim ϕ ts = op (oprim _ ϕ , ts)

real : ℝ → Term
real r = op (oreal r , λ ())

tup : ∀ {n} → (Fin n → Term) → Term
tup ts = op (otup _ , ts)

proj : ∀ {n} → Fin n → Term → Term
proj {n} i t = op (oproj n , const t)

if : Term → Term → Term → Term
if t₁ t₂ t₃ = op (oif , tup₃ t₁ t₂ t₃)

diff : Term → Term → Term
diff t₁ t₂ = op (odiff , tup₂ t₁ t₂)

solve : Term → Term → Term → Term
solve t₁ t₂ t₃ = op (osolve , tup₃ t₁ t₂ t₃)

dist : ∀ {n} → Dist → (Fin n → Term) → Term
dist D ts = op (odist _ D , ts)

assume : Term → Term
assume t = op (oassume , const t)

weight : Term → Term
weight t = op (oweight , const t)

expect : Term → Term
expect t = op (oexpect , const t)

infer : Term → Term
infer t = op (oinfer , const t)
