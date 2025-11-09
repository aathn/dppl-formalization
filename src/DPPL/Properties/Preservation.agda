open import Lib.Algebra.Reals

module DPPL.Properties.Preservation (R : Reals₀) where

open import DPPL.Regularity
open import DPPL.Syntax R
open import DPPL.SmallStep R
open import DPPL.Typing R
open import DPPL.Properties.Typing R

open import Lib.Prelude
open import Lib.Data.Vector
open import Lib.Syntax.Env

open import Data.Bool.Order using (lift)
open import Data.Finset.Base
open import Order.Lattice

open SyntaxVars
open TypingVars
open is-lattice Reg↓-lattice
open Reg↓≤

module _ (Ax : EvalAssumptions) where
  open Eval Ax
  open EvalAssumptions Ax

  record PresAssumptions : Type where
    field
      DiffPres :
        {t₀ t₁ : Tm}
        (_ : Γ ⊢ t₀ :[ e ] treals n (make c) ⇒[ P↓ , det ] treals m (make c))
        (_ : Γ ⊢ t₁ :[ e ] treals n (make c))
        (_ : c ≡ A↓ ⊎ c ≡ P↓)
        (v₀ : IsValue (t₀)) (v₁ : IsValue (t₁))
        → -----------------------------------------------------------------------------------
        Γ ⊢ Diff (_ , v₀) (_ , v₁) :[ e ] treals n (make A↓) ⇒[ A↓ , det ] treals m (make A↓)

      SolvePres :
        {t₀ t₁ t₂ : Tm}
        (_ : Γ ⊢ t₀ :[ e ] ttup 2 (pair (treal c) (treals n (make A↓))) ⇒[ A↓ , det ] treals n (make A↓))
        (_ : Γ ⊢ t₁ :[ e ] ttup 2 (pair (treal c) (treals n (make A↓))))
        (_ : Γ ⊢ t₂ :[ e ] treal (c ∩ PC↓))
        (_ : c ≡ A↓ ⊎ c ≡ C↓)
        (v₀ : IsValue t₀) (v₁ : IsValue t₁) (v₂ : IsValue t₂)
        → ---------------------------------------------------------------------------------------
        Γ ⊢ Solve (_ , v₀) (_ , v₁) (_ , v₂) :[ e ] ttup 2 (pair (treal A↓) (treals n (make A↓)))

  module Preservation (PAx : PresAssumptions) where
    open PresAssumptions PAx

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
      -- let Иi As Hty' = tlam-inv Hty reflᵢ
      -- in ?
    preservation-det-step (tprim {ϕ} {c} {e = e} H∈ Hty) (eprim {rs = rs} Heq) =
      subst (ε ⊢ real (PrimEv ϕ rs) :[ e ]_)
        (ap treal (order→∩ (subst (c ≤_) A↓-is-top !)))
        $ tpromote {Γ = ε}
          (tsub treal (lift tt) (sreal ≤-refl))
          (λ H∈ → absurd (¬mem-[] (env-sub→dom-⊆ H∈ _ hereₛ)))
          env-sub-refl
    preservation-det-step (tproj i Hty) (eproj .i Heq Hv) =
      ttup-inv (subst (_ ⊢_:[ _ ] _) Heq Hty) reflᵢ i
    preservation-det-step (tif Hty Hty₁ Hty₂ H≤) (eif {r} Heq) with is-pos r
    ... | true  = Hty₁
    ... | false = Hty₂
    preservation-det-step (tdiff Hty Hty₁ Hc) (ediff Hv₀ Hv₁) =
      DiffPres Hty Hty₁ Hc Hv₀ Hv₁
    preservation-det-step (tsolve Hty Hty₁ Hty₂ Hc) (esolve Hv₀ Hv₁ Hv₂) =
      SolvePres Hty Hty₁ Hty₂ Hc Hv₀ Hv₁ Hv₂
