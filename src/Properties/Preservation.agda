module Properties.Preservation (ℝ 𝕀 : Set) where

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.BindingSignature
open import Lib.EvalCtx

open import Function using (const)
open import Data.Vec.Functional using (map)
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.List.Relation.Binary.Sublist.Propositional using ([])

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ 𝕀
open import Properties.Typing ℝ
open import Properties.SmallStep ℝ 𝕀
open import Properties.Util

ctx-type-inv
  : ∀ {E Γ t e T}
  → DetCtx E
  → Γ ⊢ E t :[ e ] T
  → -------------------------------------------
    ∑ (e′ , T′) ∶ Eff × Type , Γ ⊢ t :[ e′ ] T′
ctx-type-inv = {!!}

preservation-ctx
  : ∀ {E Γ t₁ t₂ e T e′ T′}
  → DetCtx E
  → Γ ⊢ t₁ :[ e′ ] T′
  → Γ ⊢ t₂ :[ e′ ] T′
  → Γ ⊢ E t₁ :[ e ] T
  → -----------------
    Γ ⊢ E t₂ :[ e ] T

preservation-ctx = {!!}

module _ (Ass : EvalAssumptions) where
  open Eval Ass
  open EvalAssumptions Ass

  record PresAssumptions : Set where
    field
      PrimCoeffBound
        : ∀ {ϕ cs c}
        → PrimTy ϕ ≡ (cs , c)
        → -------------------
          c ≤ cc

      DiffPres
        : ∀ {Γ t₀ t₁ n m cs ds e}
        → (∀ i → cs i ≤ cb)
        → Γ ⊢ t₀ :[ e ] treals {n} cs ⇒[ det ] treals {m} ds
        → Γ ⊢ t₁ :[ e ] treals cs
        → (v₀ : Value t₀) (v₁ : Value t₁)
        → --------------------------------------------------------------------------
          Γ ⊢ Diff (_ , v₀) (_ , v₁) :[ e ] treals {n} (const ca) ⇒[ det ] treals ds

      SolvePres
        : ∀ {Γ t₀ t₁ t₂ Ts n c cs e}
        → Γ ⊢ t₀ :[ e ] ttup {2} Ts ⇒[ det ] treals cs
        → Ts ₀ ≡ treal c → Ts ₁ ≡ treals {n} cs
        → Γ ⊢ t₁ :[ e ] treals cs
        → Γ ⊢ t₂ :[ e ] treal cb
        → (v₀ : Value t₀) (v₁ : Value t₁) (v₂ : Value t₂)
        → -----------------------------------------------------
          Γ ⊢ Solve (_ , v₀) (_ , v₁) (_ , v₂) :[ e ] treals cs

      SamplePres
        : ∀ {D cs T rs p}
        → DistTy D ≡ (cs , T)
        → ---------------------------------
          [] ⊢ Sample D rs p .π₁ :[ det ] T

      InferPres
        : ∀ {Γ t e T p}
        → Γ ⊢ t :[ e ] tunit ⇒[ rnd ] T
        → (v : Value t)
        → --------------------------------
          Γ ⊢ Infer (_ , v) p .π₁ :[ e ] T


  module _ (PAss : PresAssumptions) where
    open PresAssumptions PAss

    preservation-det-step
      : ∀ {t t′ e T}
      → [] ⊢ t :[ e ] T
      → t →ᵈ t′
      → ---------------
        [] ⊢ t′ :[ e ] T

    preservation-det-step (tapp {ts = ts} Htype Htype₁) (eapp {t = t} Heq Hv)
      rewrite Heq with Иi As Hcof ← tabs-inv Htype refl
      with x , ∉∪ ← fresh {𝔸} (As ∪ fv (t ₀))
      rewrite subst-intro {x = x} {0} {ts ₁} (t ₀) it =
      substitution-pres-typing (Hcof x) (val-type-det Htype₁ Hv)
    preservation-det-step (tprim Hϕ Htypes Hd) (eprim Heq) =
      tsub treal 0≤ (sreal (PrimCoeffBound Hϕ))
    preservation-det-step (tproj i Htype) (eproj .i Heq Hvs) rewrite Heq =
      ttup-inv Htype refl i
    preservation-det-step (tif Htype Htype₁ Htype₂) (eif {r} _) with r >ʳ 0ʳ
    ... | true  = Htype₁
    ... | false = Htype₂
    preservation-det-step (tdiff Hcs Htype Htype₁) (ediff Hv Hv₁) =
      DiffPres Hcs Htype Htype₁ Hv Hv₁
    preservation-det-step (tsolve Htype Htype₁ Htype₂) (esolve Hv Hv₁ Hv₂) =
      SolvePres Htype refl refl Htype₁ Htype₂ Hv Hv₁ Hv₂
    preservation-det-step (texpect Htype) (eexpectdist Heq) =
      tsub treal 0≤ sub-refl
    preservation-det-step (texpect Htype) (eexpectinfer Heq Hv) =
      tsub treal 0≤ sub-refl
    preservation-det-step (tweaken Htype [] Hd) Hstep =
      preservation-det-step Htype Hstep
    preservation-det-step (tsub Htype H≤ Hsub) Hstep =
      tsub (preservation-det-step Htype Hstep) H≤ Hsub
    preservation-det-step (tpromote Htype Heq) Hstep =
      tpromote (preservation-det-step Htype Hstep) Heq

    preservation-det
      : ∀ {t t′ e T}
      → [] ⊢ t :[ e ] T
      → t →det t′
      → ---------------
        [] ⊢ t′ :[ e ] T

    preservation-det Htype (estep Hstep) = preservation-det-step Htype Hstep
    preservation-det Htype (econg Hctx Hstep) =
      let _ , Htype′ = ctx-type-inv Hctx Htype in
      preservation-ctx Hctx Htype′ (preservation-det Htype′ Hstep) Htype


    preservation-rnd-step
      : ∀ {t w s t′ w′ s′ e T}
      → [] ⊢ t :[ e ] T
      → (t , w , s) →ʳ (t′ , w′ , s′)
      → -----------------------------
        [] ⊢ t′ :[ e ] T
    preservation-rnd-step Htype (edet Hstep) = preservation-det-step Htype Hstep
    preservation-rnd-step (tassume Htype) (eassumedist Heq) rewrite Heq
      with texpect-inv Htype refl
    ... | _ , _ , Heq , Hsub =
      tsub (SamplePres Heq) 0≤ Hsub
    preservation-rnd-step (tassume Htype) (eassumeinfer Heq Hv) rewrite Heq =
      InferPres (tinfer-inv Htype refl) Hv
    preservation-rnd-step (tweight Htype) (eweight Heq) =
      ttup (λ()) []
    preservation-rnd-step (tweaken Htype [] Hd) Hstep =
      preservation-rnd-step Htype Hstep
    preservation-rnd-step (tsub Htype H≤ Hsub) Hstep =
      tsub (preservation-rnd-step Htype Hstep) H≤ Hsub
    preservation-rnd-step (tpromote Htype Heq) Hstep =
      tpromote (preservation-rnd-step Htype Hstep) Heq

    preservation-rnd
      : ∀ {t w s t′ w′ s′ e T}
      → [] ⊢ t :[ e ] T
      → (t , w , s) →rnd (t′ , w′ , s′)
      → -------------------------------
        [] ⊢ t′ :[ e ] T

    preservation-rnd Htype (estep Hstep) = preservation-rnd-step Htype Hstep
    preservation-rnd Htype (econg (E , Hctx , refl) Hstep) =
      let _ , Htype′ = ctx-type-inv Hctx Htype in
      preservation-ctx Hctx Htype′ (preservation-rnd Htype′ Hstep) Htype
