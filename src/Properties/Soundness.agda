open import Lib.Reals

module Properties.Soundness (R : Reals₀) where

open Reals R
open Interval R

open import Lib.Prelude

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε ; _◅_)

open import Syntax R
open import Typing R
open import SmallStep R
open import Properties.Preservation R
open import Properties.Progress R

module Soundness (Ass : EvalAssumptions) (PAss : PresAssumptions Ass) where
  open Eval Ass
  open Progress Ass
  open Preservation Ass PAss

  type-system-sound-det
    : ∀ {t t′ T}
    → [] ⊢ t :[ det ] T
    → t →det* t′
    → (∀ {z} → ¬ t′ →det z)
    → ---------------------
      IsValue t′

  type-system-sound-det Htype ε Hirred =
    case (progress-det Htype) λ where
      (ι₁ Hv) → Hv
      (ι₂ (_ , Hstep)) → 𝟘e $ Hirred Hstep
  type-system-sound-det Htype (Hstep ◅ Hsteps) Hirred =
    type-system-sound-det (preservation-det Htype Hstep) Hsteps Hirred

  type-system-sound-rnd
    : ∀ {t ws t′ ws′ T}
    → [] ⊢ t :[ rnd ] T
    → (t , ws) →rnd* (t′ , ws′)
    → (∀ {ws z} → ¬ (t′ , ws) →rnd z)
    → -------------------------------
      IsValue t′

  type-system-sound-rnd {ws = w , s} Htype ε Hirred =
    case (progress-rnd {w = w} {0ᴵ} {s} Htype) λ where
      (ι₁ Hv) → Hv
      (ι₂ (_ , Hstep)) → 𝟘e $ Hirred Hstep
  type-system-sound-rnd Htype (Hstep ◅ Hsteps) Hirred =
    type-system-sound-rnd (preservation-rnd Htype Hstep) Hsteps Hirred

