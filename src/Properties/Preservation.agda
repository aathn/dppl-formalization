module Properties.Preservation (ℝ : Set) where

open import Lib.Prelude
open import Lib.BindingSignature

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ

module _ (Ass : EvalAssumptions) where
  open Eval Ass

  preservation-det-step
    : ∀ {Γ t t′ T}
    → Γ ⊢ t :[ det ] T
    → t →ᵈ t′
    → -----------------
      Γ ⊢ t′ :[ det ] T

  preservation-det-step (tapp Htype Htype₁) Hstep = {!!} -- go
    where
      go
        : ∀ {t t₁ t₂ t′}
        → t →ᵈ t′
        → t ≡ app t₁ t₂
        → ------------------
          t ≡ app (abs T₁ t)
    --   go (eapp Hv) Heq = {!!}
  preservation-det-step (tprim x x₁) eprim = {!!}
  preservation-det-step (tproj i Htype) Hstep = {!!}
  preservation-det-step (tif Htype Htype₁ Htype₂) Hstep = {!!}
  preservation-det-step (tdiff x Htype Htype₁) Hstep = {!!}
  preservation-det-step (tsolve Htype Htype₁ Htype₂) Hstep = {!!}
  preservation-det-step (texpect Htype) Hstep = {!!}
  preservation-det-step (tweaken Htype H⊆ Hd) Hstep =
    tweaken (preservation-det-step Htype Hstep) H⊆ Hd
  preservation-det-step (tsub Htype 0≤ Hsub) Hstep =
    tsub (preservation-det-step Htype Hstep) 0≤ Hsub
  preservation-det-step (tpromote Htype Heq) Hstep =
    tpromote (preservation-det-step Htype Hstep) Heq

-- (tapp (tabs _) x₁) (estep (eapp x)) = {!!}
--   preservation-det (tprim x x₁) (estep eprim) = {!!}
--   preservation-det Htype (estep (eproj i x)) = {!!}
--   preservation-det Htype (estep eif) = {!!}
--   preservation-det Htype (estep (ediff x x₁)) = {!!}
--   preservation-det Htype (estep (esolve x x₁ x₂)) = {!!}
--   preservation-det Htype (estep eexpectdist) = {!!}
--   preservation-det Htype (estep (eexpectinfer x)) = {!!}
--   preservation-det Htype (econg x Hstep) = {!!}
--   preservation-det (tweaken Htype H⊆ Hd) Hstep =
--     tweaken (preservation-det Htype Hstep) H⊆ Hd
--   preservation-det (tsub Htype 0≤ Hsub) Hstep =
--     tsub (preservation-det Htype Hstep) 0≤ Hsub
--   preservation-det (tpromote Htype Heq) Hstep =
--     tpromote (preservation-det Htype Hstep) Heq

  -- preservation-det tvar Hstep = {!!}
  -- preservation-det (tabs x) Hstep = {!!}
  -- preservation-det (tapp Htype Htype₁) Hstep = {!!}
  -- preservation-det (tprim x x₁) Hstep = {!!}
  -- preservation-det treal Hstep = {!!}
  -- preservation-det (ttup x) Hstep = {!!}
  -- preservation-det (tproj i Htype) Hstep = {!!}
  -- preservation-det (tif Htype Htype₁ Htype₂) Hstep = {!!}
  -- preservation-det (tdiff x Htype Htype₁) Hstep = {!!}
  -- preservation-det (tsolve Htype Htype₁ Htype₂) Hstep = {!!}
  -- preservation-det (tdist x x₁) Hstep = {!!}
  -- preservation-det (texpect Htype) Hstep = {!!}
  -- preservation-det (tinfer Htype) Hstep = {!!}
  -- preservation-det (tweaken Htype H⊆ Hd) Hstep =
  --   tweaken (preservation-det Htype Hstep) H⊆ Hd
  -- preservation-det (tsub Htype 0≤ Hsub) Hstep =
  --   tsub (preservation-det Htype Hstep) 0≤ Hsub
  -- preservation-det (tpromote Htype Heq) Hstep =
  --   tpromote (preservation-det Htype Hstep) Heq
