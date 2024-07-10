module Properties.Preservation (ℝ : Set) where

open import Lib.Prelude
open import Lib.BindingSignature

open import Function using (const)
open import Data.Vec.Functional using (map)

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ

module _ (Ass : EvalAssumptions) where
  open Eval Ass
  open EvalAssumptions Ass

  record PresAssumptions : Set where
    field
      DiffPres
        : ∀ {Γ v₀ v₁ n m cs ds e}
        → (∀ i → cs i ≤ cb)
        → Γ ⊢ v₀ :[ e ] treals {n} cs ⇒[ det ] treals {m} ds
        → Γ ⊢ v₁ :[ e ] treals cs
        → Value v₀ → Value v₁
        → --------------------------------------------------------------
          Γ ⊢ Diff v₀ v₁ :[ e ] treals {n} (const ca) ⇒[ det ] treals ds

      SolvePres
        : ∀ {Γ v₀ v₁ v₂ Ts n c cs e}
        → Γ ⊢ v₀ :[ e ] ttup {2} Ts ⇒[ det ] treals cs
        → Ts ₀ ≡ treal c → Ts ₁ ≡ treals {n} cs
        → Γ ⊢ v₁ :[ e ] treals cs
        → Γ ⊢ v₂ :[ e ] treal c
        → Value v₀ → Value v₁ → Value v₂
        → -----------------------------------
          Γ ⊢ Solve v₀ v₁ v₂ :[ e ] treals cs

      AssumeDistPres
        : ∀ {D cs T rs p}
        → DistTy D ≡ (cs , T)
        → ---------------------------------
          [] ⊢ AssumeDist D rs p :[ det ] T

      AssumeInferPres
        : ∀ {Γ t e T p}
        → Γ ⊢ t :[ e ] tunit ⇒[ rnd ] T
        → -----------------------------
          Γ ⊢ AssumeInfer t p :[ e ] T


  module _ (PAss : PresAssumptions) where
    open PresAssumptions PAss

    preservation-det-step
      : ∀ {Γ t t′ e T}
      → Γ ⊢ t :[ e ] T
      → t →ᵈ t′
      → ---------------
        Γ ⊢ t′ :[ e ] T

    preservation-det-step (tapp Htype Htype₁) (eapp Heq Hv) rewrite Heq = {!!}
    preservation-det-step (tprim Hϕ Htypes) (eprim Heq) =
      tweaken (tsub treal {!!} {!!}) {!!} {!!}
    preservation-det-step (tproj i Htype) (eproj .i Heq Hvs) rewrite Heq =
      {!!}
    preservation-det-step (tif Htype Htype₁ Htype₂) (eif {r} _) with r >ʳ 0ʳ
    ... | true  = Htype₁
    ... | false = Htype₂
    preservation-det-step (tdiff Hcs Htype Htype₁) (ediff Hv Hv₁) =
      DiffPres Hcs Htype Htype₁ Hv Hv₁
    preservation-det-step (tsolve Htype Htype₁ Htype₂) (esolve Hv Hv₁ Hv₂) = {!!}
      -- SolvePres Htype Htype₁ Htype₂ Hv Hv₁ Hv₂
    preservation-det-step (texpect Htype) (eexpectdist Heq) =
      tweaken (tsub treal 0≤ {!!}) {!!} {!!}
    preservation-det-step (texpect Htype) (eexpectinfer Heq Hv) =
      tweaken (tsub treal 0≤ {!!}) {!!} {!!}
    preservation-det-step (tweaken Htype H⊆ Hd) Hstep =
      tweaken (preservation-det-step Htype Hstep) H⊆ Hd
    preservation-det-step (tsub Htype H≤ Hsub) Hstep =
      tsub (preservation-det-step Htype Hstep) H≤ Hsub
    preservation-det-step (tpromote Htype Heq) Hstep =
      tpromote (preservation-det-step Htype Hstep) Heq

    preservation-rnd-step
      : ∀ {Γ t w s t′ w′ s′ e T}
      → Γ ⊢ t :[ e ] T
      → (t , w , s) →ʳ (t′ , w′ , s′)
      → -----------------------------
        Γ ⊢ t′ :[ e ] T
    preservation-rnd-step Htype (edet Hstep) = preservation-det-step Htype Hstep
    preservation-rnd-step (tassume Htype) (eassumedist Heq) =
      tweaken (tsub (AssumeDistPres {!!}) 0≤ {!!}) {!!} {!!}
    preservation-rnd-step (tassume Htype) (eassumeinfer Heq Hv) = {!!}
    preservation-rnd-step (tweight Htype) (eweight Heq) =
      tweaken (ttup λ()) {!!} {!!}
    preservation-rnd-step (tweaken Htype H⊆ Hd) Hstep =
      tweaken (preservation-rnd-step Htype Hstep) H⊆ Hd
    preservation-rnd-step (tsub Htype H≤ Hsub) Hstep =
      tsub (preservation-rnd-step Htype Hstep) H≤ Hsub
    preservation-rnd-step (tpromote Htype Heq) Hstep =
      tpromote (preservation-rnd-step Htype Hstep) Heq
