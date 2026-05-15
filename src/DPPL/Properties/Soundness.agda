open import Lib.Algebra.Reals
open import Lib.Syntax.Env
open import Lib.Prelude

module DPPL.Properties.Soundness (R : Reals₀) where

open import DPPL.Properties.Preservation R
open import DPPL.Properties.Progress R
open import DPPL.Properties.Typing R
open import DPPL.SmallStep R
open import DPPL.Syntax R
open import DPPL.Typing R

open SyntaxVars

module Soundness (Ax : EvalAssumptions) (PAx : PresAssumptions Ax) where
  open Preservation Ax PAx
  open Progress Ax
  open Eval Ax

  type-system-sound :
    (_ : ε ⊢ t ∶ T)
    (_ : t →det* t')
    (_ : ∀ {z} → ¬ t' →det z)
    → -----------------------
    is-value t'
  type-system-sound Htype nil Hirred =
    case progress Htype of λ where
      (inl Hv)          → Hv
      (inr (_ , Hstep)) → absurd (Hirred Hstep)
  type-system-sound Htype (step Hstep Hsteps) Hirred =
    type-system-sound (preservation Htype Hstep) Hsteps Hirred
