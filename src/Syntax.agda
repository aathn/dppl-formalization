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

-- Syntax shorthands

pattern 0ꟳ = zero
pattern 1ꟳ = succ zero
pattern 2ꟳ = succ (succ zero)

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

app : Vector Term 2 → Term
app ts = op (oapp , ts)

prim : (ϕ : Prim) → Vector Term (PrimAr ϕ) → Term
prim ϕ ts = op (oprim ϕ , ts)

real : ℝ → Term
real r = op (oreal r , λ ())

tup : ∀ {n} → Vector Term n → Term
tup ts = op (otup _ , ts)

proj : ∀ {n} → Fin n → Term → Term
proj {n} i t = op (oproj n , const t)

if : Vector Term 3 → Term
if ts = op (oif , ts)

diff : Vector Term 2 → Term
diff ts = op (odiff , ts)

solve : Vector Term 3 → Term
solve ts = op (osolve , ts)

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
