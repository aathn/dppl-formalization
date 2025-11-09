open import Lib.Algebra.Reals

module DPPL.Properties.Preservation (R : Reals₀) where

open import DPPL.Syntax R
open import DPPL.Typing R
open import DPPL.SmallStep R

open import Lib.Prelude
open import Lib.Syntax.Env

open import Data.Finset.Base

open SyntaxVars

module _ (Ax : EvalAssumptions) where
  open Eval Ax
  preservation-det-step :
    (_ : ε ⊢ t :[ e ] T)
    (_ : t →ᵈ t')
    → -------------------
    ε ⊢ t' :[ e ] T
  preservation-det-step (tsub Hty H≤ H<:) Hstep =
    tsub (preservation-det-step Hty Hstep) H≤ H<:
  preservation-det-step (tpromote {Γ = Γ} Hty H≤ H⊆) Hstep
    rewrite Id≃path.from (env-sub-nil-inv Γ H⊆) = tpromote
     (preservation-det-step Hty Hstep)
     (λ H∈ → absurd (¬mem-[] (env-sub→dom-⊆ H∈ _ hereₛ)))
     env-sub-refl
  preservation-det-step (tapp Hty Hty₁) (eapp Heq Hv) = {!!}
  preservation-det-step (tprim H∈ Hty) (eprim Heq) = {!!}
  preservation-det-step (tproj i Hty) (eproj .i Heq Hv) = {!!}
  preservation-det-step (tif Hty Hty₁ Hty₂ H≤) (eif Heq) = {!!}
  preservation-det-step (tdiff Hty Hty₁ Hc) (ediff Hv₀ Hv₁) = {!!}
  preservation-det-step (tsolve Hty Hty₁ Hty₂ Hc) (esolve Hv₀ Hv₁ Hv₂) = {!!}
