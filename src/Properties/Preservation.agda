module Properties.Preservation (ℝ : Set) where

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.BindingSignature

open import Function using (const)
open import Data.Vec.Functional using (map)
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.List.Relation.Binary.Sublist.Propositional using ([])

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ
open import Properties.Typing ℝ
open import Properties.SmallStep ℝ
open import Properties.Util

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
      tweaken (tsub treal 0≤ (sreal (PrimCoeffBound Hϕ))) []-⊆ Hd
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
      tweaken (tsub treal 0≤ sub-refl) []-⊆ (well-typed-distinct Htype)
    preservation-det-step (texpect Htype) (eexpectinfer Heq Hv) =
      tweaken (tsub treal 0≤ sub-refl) []-⊆ (well-typed-distinct Htype)
    preservation-det-step (tweaken Htype [] Hd) Hstep =
      tweaken (preservation-det-step Htype Hstep) [] Hd
    preservation-det-step (tsub Htype H≤ Hsub) Hstep =
      tsub (preservation-det-step Htype Hstep) H≤ Hsub
    preservation-det-step (tpromote Htype Heq) Hstep =
      tpromote (preservation-det-step Htype Hstep) Heq

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
      tweaken (tsub (AssumeDistPres Heq) 0≤ Hsub) []-⊆ (well-typed-distinct Htype)
    preservation-rnd-step (tassume Htype) (eassumeinfer Heq Hv) rewrite Heq =
      AssumeInferPres (tinfer-inv Htype refl)
    preservation-rnd-step (tweight Htype) (eweight Heq) =
      tweaken (ttup (λ()) []) []-⊆ (well-typed-distinct Htype)
    preservation-rnd-step (tweaken Htype [] Hd) Hstep =
      tweaken (preservation-rnd-step Htype Hstep) [] Hd
    preservation-rnd-step (tsub Htype H≤ Hsub) Hstep =
      tsub (preservation-rnd-step Htype Hstep) H≤ Hsub
    preservation-rnd-step (tpromote Htype Heq) Hstep =
      tpromote (preservation-rnd-step Htype Hstep) Heq
