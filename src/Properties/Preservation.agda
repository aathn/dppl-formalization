module Properties.Preservation (ℝ : Set) where

open import Lib.Prelude
open import Lib.BindingSignature

open import Function using (const)

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ

module _ (Ass : EvalAssumptions) where
  open Eval Ass
  open EvalAssumptions Ass

  preservation-det-step
    : ∀ {Γ t t′ e T}
    → Γ ⊢ t :[ e ] T
    → t →ᵈ t′
    → -----------------
      Γ ⊢ t′ :[ e ] T

  preservation-det-step (tapp Htype Htype₁) (eapp Heq Hv) rewrite Heq = {!!}
  preservation-det-step (tprim Hϕ Htypes) (eprim Heq) = {!!}
  preservation-det-step (tproj i Htype) (eproj .i Heq Hvs) rewrite Heq = {!!}
  preservation-det-step (tif Htype Htype₁ Htype₂) (eif {r} _) with r >ʳ 0ʳ
  ... | true  = Htype₁
  ... | false = Htype₂
  preservation-det-step (tdiff Hcs Htype Htype₁) (ediff Hv Hv₁) = {!!}
  preservation-det-step (tsolve Htype Htype₁ Htype₂) (esolve Hv Hv₁ Hv₂) = {!!}
  preservation-det-step (texpect Htype) (eexpectdist x) = {!!}
  preservation-det-step (texpect Htype) (eexpectinfer x x₁) = {!!}
  preservation-det-step (tweaken Htype H⊆ Hd) Hstep =
    tweaken (preservation-det-step Htype Hstep) H⊆ Hd
  preservation-det-step (tsub Htype H≤ Hsub) Hstep = {!!}
    -- tsub (preservation-det-step Htype Hstep) 0≤ Hsub
  preservation-det-step (tpromote Htype Heq) Hstep =
    tpromote (preservation-det-step Htype Hstep) Heq

  preservation-rnd-step
    : ∀ {Γ t w s t′ w′ s′ e T}
    → Γ ⊢ t :[ e ] T
    → (t , w , s) →ʳ (t′ , w′ , s′)
    → -----------------------------
      Γ ⊢ t′ :[ e ] T
  preservation-rnd-step Htype (edet Hstep) = preservation-det-step Htype Hstep
  preservation-rnd-step (tassume Htype) (eassumedist x) = {!!}
  preservation-rnd-step (tassume Htype) (eassumeinfer x x₁) = {!!}
  preservation-rnd-step (tweight Htype) (eweight x) = {!!}
  preservation-rnd-step (tweaken Htype x x₁) Hstep = {!!}
  preservation-rnd-step (tsub Htype x x₁) Hstep = {!!}
  preservation-rnd-step (tpromote Htype x) Hstep = {!!}
