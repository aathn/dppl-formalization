open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.Support
open import Lib.BindingSignature

module Syntax (ℝ : Set) where

data Coeff : Set where
  ca : Coeff
  cb : Coeff
  cc : Coeff

data Eff : Set where
  edet : Eff
  ernd : Eff

data Type : Set where
  treal   : Coeff → Type
  _⇒[_]_ : Type → Eff → Type → Type
  ttup    : Array Type → Type
  tdist   : Type → Type

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
  where
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
    odist   : ℕ → TermOp
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
  length (TermAr (odist n))     = n
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
  index  (TermAr (odist _))   i = 0
  index  (TermAr oassume)     i = 0
  index  (TermAr oweight)     i = 0
  index  (TermAr oinfer)      i = 0
  index  (TermAr oexpect)     i = 0

Term : Set
Term = Trm TermSig

_≈>_ : 𝔸 → Term → Term → Term
(a ≈> u) t = Subst.substTrm t ρ
  where
  ρ : ℕ𝔸 → Term
  ρ (ι₁ x) = bvar x
  ρ (ι₂ y) = case (a ≐ y) λ
    { equ     → u
    ; (neq _) → fvar y
    }
