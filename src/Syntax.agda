open import Lib.Reals

module Syntax (R : Reals₀) where

open Reals R

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.Support
open import Lib.BindingSignature

open import Data.Vec.Functional using (map ; fromList)

Coeff : Set
Coeff = Fin 3

pattern A = zero {n = 2}
pattern P = succ {n = 2} zero
pattern N = succ {n = 2} (succ zero)

Eff : Set
Eff = Fin 2

pattern det = zero {n = 1}
pattern rnd = succ {n = 1} zero

-- Types

data Type : Set where
  treal   : Coeff → Type
  _⇒[_]_  : Type → Eff → Type → Type
  ttup    : (n : ℕ) → Vector Type n → Type
  tdist   : Type → Type

-- Terms

data Dist : Set where
  dnormal : Dist
  dbeta   : Dist
  dwiener : Dist

DistAr : Dist → ℕ
DistAr dnormal = 2
DistAr dbeta   = 2
DistAr dwiener = 0

data Prim : Set where
  padd    : Prim
  pmul    : Prim
  psin    : Prim
  pwiener : ℝ → Prim

PrimAr : Prim → ℕ
PrimAr padd = 2
PrimAr pmul = 2
PrimAr psin = 1
PrimAr (pwiener _) = 1

TermSig : Sig
TermSig = mkSig TermOp TermAr
  module _ where
  data TermOp : Set where
    abs    : Type → TermOp
    app    : TermOp
    prim   : Prim → TermOp
    oreal  : ℝ → TermOp
    tup    : ℕ → TermOp
    proj   : (n : ℕ) → Fin n → TermOp
    if     : TermOp
    diff   : TermOp
    solve  : TermOp
    dist   : Dist → TermOp
    assume : TermOp
    weight : TermOp
    infer  : TermOp
  TermAr : TermOp → Array ℕ
  length (TermAr (abs _))    = 1
  length (TermAr app)        = 2
  length (TermAr (prim ϕ))   = PrimAr ϕ
  length (TermAr (oreal _))  = 0
  length (TermAr (tup n))    = n
  length (TermAr (proj _ _)) = 1
  length (TermAr if)         = 3
  length (TermAr diff)       = 2
  length (TermAr solve)      = 3
  length (TermAr (dist D))   = DistAr D
  length (TermAr assume)     = 1
  length (TermAr weight)     = 1
  length (TermAr infer)      = 1
  index  (TermAr (abs _))    = const 1
  index  (TermAr _)          = const 0

Term : Set
Term = Trm TermSig

instance
  lnsTerm = lnsTrm

-- Syntax shorthands

pattern ₀ = zero
pattern ₁ = succ zero
pattern ₂ = succ (succ zero)

infix 25 _▸_
pattern _▸_ x y = op (x , y)

tunit : Type
tunit = ttup 0 λ()

treals : (n : ℕ) → Vector Coeff n → Type
treals n cs = ttup n $ map treal cs

unit : Term
unit = tup 0 ▸ λ()

real : ℝ → Term
real r = oreal r ▸ λ ()

-- Metavariables

variable
  m n  : ℕ
  r    : ℝ
  ϕ    : Prim
  D    : Dist
  T T′ : Type
  e e′ : Eff
  c c′ : Coeff
  t t′ : Term
