open import Lib.Algebra.Reals

module DPPL.Syntax (R : Reals₀) where

open Reals R hiding (_+_)

open import DPPL.Regularity

open import Lib.Prelude
open import Lib.Data.Vector
open import Lib.LocallyNameless.Support
open import Lib.LocallyNameless.BindingSignature
open import Lib.Order.Bool

open import Data.Bool.Base using (Discrete-Bool)
open import Data.Dec.Base
open import Data.Nat.Base using (Nat-is-set)
open import Data.Fin.Properties
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

-- Lemmas about type syntax

treal-inj : ∀ {c c'} → treal c ≡ treal c' → c ≡ c'
treal-inj {c} = ap λ where
  (treal c) → c
  _ → c

tarr-inj : ∀ {S S' e e' T T'} → S ⇒[ e ] T ≡ S' ⇒[ e' ] T' → (S , e , T) ≡ (S' , e' , T')
tarr-inj {S} {e = e} {T = T} = ap λ where
  (S ⇒[ e ] T) → S , e , T
  _ → S , e , T

ttup-inj : ∀ {n m Ts Ts'} → ttup n Ts ≡ ttup m Ts' → (n , Ts) ≡ (m , Ts')
ttup-inj {n} {Ts = Ts} = ap λ where
  (ttup n Ts) → n , Ts
  _ → n , Ts

tdist-inj : ∀ {T T'} → tdist T ≡ tdist T' → T ≡ T'
tdist-inj {T} = ap λ where
  (tdist T) → T
  _ → T

is-treal is-tarr is-ttup is-tdist : Ty → Type
is-treal (treal _)   = ⊤
is-treal _           = ⊥
is-tarr (_ ⇒[ _ ] _) = ⊤
is-tarr _            = ⊥
is-ttup (ttup _ _)   = ⊤
is-ttup _            = ⊥
is-tdist (tdist _)   = ⊤
is-tdist _           = ⊥

instance
  Discrete-Ty : Discrete Ty
  Discrete-Ty .decide = go where
    go : _
    go (treal c) (treal c') with c ≡? c'
    ... | yes c≡c' = yes (ap treal c≡c')
    ... | no  c≠c' = no  (c≠c' ∘ treal-inj)
    go (S ⇒[ e ] T) (S' ⇒[ e' ] T') with go S S'
    ... | no  S≠S' = no (S≠S' ∘ ap fst ∘ tarr-inj)
    ... | yes S≡S' with e ≡? e'
    ... | no  e≠e' = no (e≠e' ∘ ap (fst ∘ snd) ∘ tarr-inj)
    ... | yes e≡e' with go T T'
    ... | no  T≠T' = no (T≠T' ∘ ap (snd ∘ snd) ∘ tarr-inj)
    ... | yes T≡T' = yes (λ i → S≡S' i ⇒[ e≡e' i ] T≡T' i)
    go (ttup n Ts) (ttup m Ts') with n ≡ᵢ? m
    ... | no n≠m = no λ p → n≠m (Id≃path.from (ap fst (ttup-inj p)))
    ... | yes reflᵢ with Dec-Fin-∀ ⦃ λ {i} → go (Ts i) (Ts' i) ⦄
    ... | no  Ts≠Ts' = no λ q →
      Ts≠Ts' (is-set→cast-pathp (Ty ^_) Nat-is-set (ap snd (ttup-inj q)) $ₚ_)
    ... | yes Ts≡Ts' = yes (ap (ttup n) (funext Ts≡Ts'))
    go (tdist T) (tdist T') with go T T'
    ... | no  T≠T' = no (T≠T' ∘ tdist-inj)
    ... | yes T≡T' = yes (ap tdist T≡T')

    go (treal _)    (_ ⇒[ _ ] _) = no λ p → subst is-treal p tt
    go (treal _)    (ttup _ _)   = no λ p → subst is-treal p tt
    go (treal _)    (tdist _)    = no λ p → subst is-treal p tt
    go (_ ⇒[ _ ] _) (treal _)    = no λ p → subst is-tarr p tt
    go (_ ⇒[ _ ] _) (ttup _ _)   = no λ p → subst is-tarr p tt
    go (_ ⇒[ _ ] _) (tdist _)    = no λ p → subst is-tarr p tt
    go (ttup _ _)   (treal _)    = no λ p → subst is-ttup p tt
    go (ttup _ _)   (_ ⇒[ _ ] _) = no λ p → subst is-ttup p tt
    go (ttup _ _)   (tdist _)    = no λ p → subst is-ttup p tt
    go (tdist _)    (treal _)    = no λ p → subst is-tdist p tt
    go (tdist _)    (_ ⇒[ _ ] _) = no λ p → subst is-tdist p tt
    go (tdist _)    (ttup _ _)   = no λ p → subst is-tdist p tt

Ty-is-set : is-set Ty
Ty-is-set = Discrete→is-set Discrete-Ty

instance
  H-Level-Ty : ∀ {n} → H-Level Ty (2 + n)
  H-Level-Ty = basic-instance 2 Ty-is-set
