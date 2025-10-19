open import Lib.Algebra.Reals

module DPPL.Properties.Determinism (R : Reals₀) where

open import DPPL.Syntax R
open import DPPL.SmallStep R
open import DPPL.Properties.SmallStep R

open import Lib.Prelude
open import Lib.Data.Vector
open import Lib.LocallyNameless.BindingSignature
open import Lib.Syntax.EvalCtx
open import Lib.Syntax.Substitution

open import Data.Nat.Base using (Nat-is-set)

module _ (Ax : EvalAssumptions) where
  open EvalAssumptions Ax
  open Eval Ax
  open Step Ax

  →ᵈ-deterministic : Deterministic _→ᵈ_
  →ᵈ-deterministic (eapp Heq Hv) (eapp Heq' Hv') =
    ap (λ t → (0 ≈> _) (t ₀)) $ is-set→cast-pathp {q = refl} (Tm ^_) Nat-is-set
      (ap snd (op-inj (sym Heq ∙ Heq')))
  →ᵈ-deterministic (eprim {ϕ = ϕ} Heq) (eprim Heq') =
    ap (real ∘ PrimEv ϕ) (ext λ i → real-inj $ op-inj' (sym Heq ∙ Heq') $ₚ i)
  →ᵈ-deterministic (eproj _ Heq _) (eproj _ Heq' _) = op-inj' (sym Heq ∙ Heq') $ₚ _
  →ᵈ-deterministic (eif Heq) (eif Heq') =
    ap (λ r → if is-pos r then _ else _) (real-inj $ sym Heq ∙ Heq')
  →ᵈ-deterministic (ediff Hv₀ Hv₁) (ediff Hv₀' Hv₁') i =
    Diff (_ , IsValue-is-prop Hv₀ Hv₀' i) (_ , IsValue-is-prop Hv₁ Hv₁' i)
  →ᵈ-deterministic (esolve Hv₀ Hv₁ Hv₂) (esolve Hv₀' Hv₁' Hv₂') i =
    Solve
      (_ , IsValue-is-prop Hv₀ Hv₀' i)
      (_ , IsValue-is-prop Hv₁ Hv₁' i)
      (_ , IsValue-is-prop Hv₂ Hv₂' i)


  DetCtx-cannot-step :
    {E : Tm → Tm}
    {t u : Tm}
    (_ : DetCtx E)
    (_ : ¬ IsValue t)
    → ---------------
    ¬ E t →ᵈ u

  DetCtx-cannot-step (ectx _) Ht (eapp x x₁) = {!!}
  DetCtx-cannot-step (ectx _) Ht (eprim x) = {!!}
  DetCtx-cannot-step (ectx _) Ht (eproj i x x₁) = {!!}
  DetCtx-cannot-step (ectx _) Ht (eif x) = {!!}
  DetCtx-cannot-step (ectx _) Ht (ediff v₀ v₁) = {!!}
  DetCtx-cannot-step (ectx _) Ht (esolve v₀ v₁ v₂) = {!!}
  -- DetCtx-cannot-step (ectx {j = ₀} _) Ht (eapp refl _) = Ht vabs
  -- DetCtx-cannot-step (ectx {j = ₁} _) Ht (eapp _ Hv) = Ht Hv
  -- DetCtx-cannot-step {t = t} (ectx {j = j} {ts} _) Ht (eprim {rs = rs} Heq) =
  --   Ht (subst IsValue Heq' (vreal {rs j}))
  --   where Heq' = proof                      real (rs j)
  --                ≡[ symm $ ap (_$ j) Heq ]  updateAt ts j (const t) j
  --                ≡[ updateAt-updates j ts ] t
  --                qed
  -- DetCtx-cannot-step (ectx {j = ₀} _) Ht (eproj i refl Hvs) = Ht (vtup Hvs)
  -- DetCtx-cannot-step (ectx {j = ₀} _) Ht (eif refl) = Ht vreal
  -- DetCtx-cannot-step (ectx {j = ₀} _) Ht (ediff v₀ v₁) = Ht v₀
  -- DetCtx-cannot-step (ectx {j = ₁} _) Ht (ediff v₀ v₁) = Ht v₁
  -- DetCtx-cannot-step (ectx {j = ₀} _) Ht (esolve v₀ v₁ v₂) = Ht v₀
  -- DetCtx-cannot-step (ectx {j = ₁} _) Ht (esolve v₀ v₁ v₂) = Ht v₁
  -- DetCtx-cannot-step (ectx {j = ₂} _) Ht (esolve v₀ v₁ v₂) = Ht v₂

  -- →det-deterministic : Deterministic _≡_ _→det_
  -- →det-deterministic =
  --   CongCls-deterministic →ᵈ-deterministic
  --     (λ Hctx1 Hctx2 Ht Hu Heq →
  --       DetCtx-unique Hctx1 Hctx2
  --         (λ Hv → value-cannot-step-det Hv Ht)
  --         (λ Hv → value-cannot-step-det Hv Hu)
  --         Heq)
  --     (λ Hctx Ht →
  --       DetCtx-cannot-step Hctx
  --         (λ Hv → value-cannot-step-det Hv Ht))


  -- →ʳ-deterministic : Deterministic _≡_ _→ʳ_

  -- →ʳ-deterministic (edet Hstep) (edet Hstep') =
  --   ap (λ t → t , _) (→ᵈ-deterministic Hstep Hstep')
  -- →ʳ-deterministic (eweight Heq) (eweight Heq')
  --   rewrite Heq with refl ← Heq' = refl
  -- →ʳ-deterministic (eassumedist {D = D} Heq) (eassumedist Heq')
  --   rewrite Heq with refl , Hmap ← op-injective Heq' =
  --   ap (λ rs → Sample D rs _ .π₁ , _) $ vmap-injective real (λ {refl → refl}) Hmap
  -- →ʳ-deterministic (eassumeinfer Heq Hv) (eassumeinfer Heq' Hv')
  --   rewrite Heq with refl ← Heq' with refl ← value-irrelevant Hv Hv' = refl
  -- →ʳ-deterministic (eassumedist Heq) (eassumeinfer Heq' _)
  --   rewrite Heq with () ← Heq'
  -- →ʳ-deterministic (eassumeinfer Heq _) (eassumedist Heq')
  --   rewrite Heq with () ← Heq'

  -- RndCtx-unique :
  --   {E E' : Term × ℝ × List 𝕀 → Term × ℝ × List 𝕀}
  --   {t u : Term × ℝ × List 𝕀}
  --   (_ : RndCtx E)
  --   (_ : RndCtx E')
  --   (_ : ¬ IsValue (t .π₁))
  --   (_ : ¬ IsValue (u .π₁))
  --   → -------------------------
  --   E t ≡ E' u → E ≡ E' × t ≡ u

  -- RndCtx-unique (E , Hctx , refl) (E' , Hctx' , refl) Ht Hu Heq
  --   with Heq' , refl ← ,-injective Heq
  --   with refl , refl ← DetCtx-unique Hctx Hctx' Ht Hu Heq' = refl , refl

  -- RndCtx-cannot-step :
  --   {E : Term × ℝ × List 𝕀 → Term × ℝ × List 𝕀}
  --   {t u : Term × ℝ × List 𝕀}
  --   (_ : RndCtx E)
  --   (_ : ¬ IsValue (t .π₁))
  --   → ---------------------
  --   ¬ E t →ʳ u

  -- RndCtx-cannot-step (_ , ectx Hvs , refl) Ht (edet Hstep) =
  --   DetCtx-cannot-step (ectx Hvs) Ht Hstep
  -- RndCtx-cannot-step (_ , ectx {j = ₀} _ , refl) Ht (eweight refl) = Ht vreal
  -- RndCtx-cannot-step (_ , ectx {j = ₀} _ , refl) Ht (eassumedist refl) =
  --   Ht (vdist (λ _ → vreal))
  -- RndCtx-cannot-step (_ , ectx {j = ₀} _ , refl) Ht (eassumeinfer refl v) =
  --   Ht (vinfer v)

  -- →rnd-deterministic : Deterministic _≡_ _→rnd_
  -- →rnd-deterministic =
  --   CongCls-deterministic →ʳ-deterministic
  --     (λ Hctx1 Hctx2 Ht Hu Heq →
  --       RndCtx-unique Hctx1 Hctx2
  --         (λ Hv → value-cannot-step-rnd Hv Ht)
  --         (λ Hv → value-cannot-step-rnd Hv Hu)
  --         Heq)
  --     (λ Hctx Ht →
  --       RndCtx-cannot-step Hctx
  --         (λ Hv → value-cannot-step-rnd Hv Ht))
