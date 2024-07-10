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
    oproj   : (n : ℕ) → Fin n → TermOp
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
  length (TermAr (oproj _ _)) = 1
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

pattern ₀ = zero
pattern ₁ = succ zero
pattern ₂ = succ (succ zero)

tunit : Type
tunit = ttup {0} λ()

treals : ∀ {n} → Vector Coeff n → Type
treals cs = ttup $ map treal cs

abs : Type → Vector Term 1 → Term
abs T t = op (oabs T , t)

app : Vector Term 2 → Term
app ts = op (oapp , ts)

prim : (ϕ : Prim) → Vector Term (PrimAr ϕ) → Term
prim ϕ ts = op (oprim ϕ , ts)

real : ℝ → Term
real r = op (oreal r , λ ())

tup : ∀ {n} → Vector Term n → Term
tup ts = op (otup _ , ts)

proj : ∀ {n} → Fin n → Vector Term 1 → Term
proj {n} i t = op (oproj n i , t)

if : Vector Term 3 → Term
if ts = op (oif , ts)

diff : Vector Term 2 → Term
diff ts = op (odiff , ts)

solve : Vector Term 3 → Term
solve ts = op (osolve , ts)

dist : (D : Dist) → Vector Term (DistAr D) → Term
dist D ts = op (odist D , ts)

assume : Vector Term 1 → Term
assume t = op (oassume , t)

weight : Vector Term 1 → Term
weight t = op (oweight , t)

expect : Vector Term 1 → Term
expect t = op (oexpect , t)

infer : Vector Term 1 → Term
infer t = op (oinfer , t)

unit : Term
unit = tup {0} λ()
