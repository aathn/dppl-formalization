open import Lib.Algebra.Reals

module DPPL.Syntax (R : Reals₀) where

open Reals R

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
  ttup    : (n : Nat) → Vector Ty n → Ty
  tdist   : Ty → Ty
  treal  : Reg↓ → Ty
  _⇒[_]_ : Ty → Eff → Ty → Ty

-- Terms

data Dist : Type where
  dnormal : Dist
  dbeta   : Dist
  dwiener : Dist

DistAr : Dist → Nat
DistAr dnormal = 2
DistAr dbeta   = 2
DistAr dwiener = 0

data Prim : Type where
  padd    : Prim
  pmul    : Prim
  psin    : Prim
  pwiener : ℝ → Prim

PrimAr : Prim → Nat
PrimAr padd = 2
PrimAr pmul = 2
PrimAr psin = 1
PrimAr (pwiener _) = 1

TmSig : Sig
TmSig = mkSig TmOp TmAr
  module _ where
  data TmOp : Type where
    abs    : Ty → TmOp
    app    : TmOp
    prim   : Prim → TmOp
    oreal  : ℝ → TmOp
    tup    : Nat → TmOp
    proj   : (n : Nat) → Fin n → TmOp
    if     : TmOp
    diff   : TmOp
    solve  : TmOp
    dist   : Dist → TmOp
    assume : TmOp
    weight : TmOp
    infer  : TmOp
  TmAr : TmOp → Array Nat
  length (TmAr (abs _))    = 1
  length (TmAr app)        = 2
  length (TmAr (prim ϕ))   = PrimAr ϕ
  length (TmAr (oreal _))  = 0
  length (TmAr (tup n))    = n
  length (TmAr (proj _ _)) = 1
  length (TmAr if)         = 3
  length (TmAr diff)       = 2
  length (TmAr solve)      = 3
  length (TmAr (dist D))   = DistAr D
  length (TmAr assume)     = 1
  length (TmAr weight)     = 1
  length (TmAr infer)      = 1
  index  (TmAr (abs _)) _  = 1
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

treals : (n : Nat) → Vector ⌞ Reg↓ ⌟ n → Ty
treals n cs = ttup n $ map treal cs

unit : Tm
unit = tup 0 ▸ λ()

real : ℝ → Tm
real r = oreal r ▸ λ ()

-- Metavariables

module MetaVars where
  variable
    m n  : Nat
    r    : ℝ
    ϕ    : Prim
    D    : Dist
    T T' : Ty
    e e' : Eff
    c c' : Reg↓
    t t' : Tm
