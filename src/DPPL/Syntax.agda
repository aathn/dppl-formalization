open import Lib.Algebra.Reals

module DPPL.Syntax (R : Reals₀) where

open Reals R hiding (_+_)

open import DPPL.Regularity

open import Lib.Prelude
open import Lib.Data.Vector
open import Lib.LocallyNameless.Support
open import Lib.LocallyNameless.BindingSignature

open import Cat.Instances.Shape.Interval
open import Order.Base

Eff : Type
Eff = Bool

Eff-poset : Poset lzero lzero
Eff-poset = Bool-poset

module Eff≤ = Poset Eff-poset

pattern det = false
pattern rnd = true

-- Types

data Ty : Type where
  treal  : Reg↓ → Ty
  _⇒[_]_ : Ty → Eff → Ty → Ty
  ttup   : (n : Nat) → Ty ^ n → Ty
  tdist  : Ty → Ty

instance
  Discrete-Ty : Discrete Ty
  Discrete-Ty = {!!}

opaque
  Ty-is-set : is-set Ty
  Ty-is-set = Discrete→is-set Discrete-Ty

instance
  H-Level-Ty : ∀ {n} → H-Level Ty (2 + n)
  H-Level-Ty = basic-instance 2 Ty-is-set

-- Terms

data Prim : Type where
  padd    : Prim
  pmul    : Prim
  psin    : Prim
  pnormal : Prim
  pbeta   : Prim
  pwiener : Prim

PrimAr : Prim → Nat
PrimAr padd = 2
PrimAr pmul = 2
PrimAr psin = 1
PrimAr pnormal = 3
PrimAr pbeta   = 3
PrimAr pwiener = 2

TmSig : Sig
TmSig = mkSig TmOp TmAr
  module _ where
  data TmOp : Type where
    lam    : Ty → TmOp
    app    : TmOp
    prim   : Prim → TmOp
    oreal  : ℝ → TmOp
    tup    : Nat → TmOp
    proj   : (n : Nat) → Fin n → TmOp
    if     : TmOp
    diff   : TmOp
    solve  : TmOp
    osample : TmOp
    assume : TmOp
    weight : TmOp
    infer  : TmOp
  TmAr : TmOp → Array Nat
  length (TmAr (lam _))    = 1
  length (TmAr app)        = 2
  length (TmAr (prim ϕ))   = PrimAr ϕ
  length (TmAr (oreal _))  = 0
  length (TmAr (tup n))    = n
  length (TmAr (proj _ _)) = 1
  length (TmAr if)         = 3
  length (TmAr diff)       = 2
  length (TmAr solve)      = 3
  length (TmAr osample)    = 0
  length (TmAr assume)     = 1
  length (TmAr weight)     = 1
  length (TmAr infer)      = 1
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

sample : Tm
sample = osample ▸ λ ()

-- Metavariables

module SyntaxVars where
  variable
    m n  : Nat
    r    : ℝ
    ϕ    : Prim
    T T' : Ty
    e e' : Eff
    c c' : Reg↓
    t t' : Tm
