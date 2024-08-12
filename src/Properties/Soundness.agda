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

  type-system-sound
    : ∀ {t ws t′ ws′ T}
    → [] ⊢ t :[ rnd ] T
    → (t , ws) →rnd* (t′ , ws′)
    → (∀ {ws z} → ¬ (t′ , ws) →rnd z)
    → -------------------------------
      Value t′

  type-system-sound {ws = w , s} Htype ε Hirred =
    case (progress-rnd {w = w} {0ᴵ} {s} Htype) λ where
      (ι₁ Hv) → Hv
      (ι₂ (_ , Hstep)) → 𝟘e $ Hirred Hstep
  type-system-sound Htype (Hstep ◅ Hsteps) Hirred =
    type-system-sound (preservation-rnd Htype Hstep) Hsteps Hirred
