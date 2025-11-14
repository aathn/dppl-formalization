open import Lib.Algebra.Reals

module DPPL.Properties.Determinism (R : Reals₀) where

open import DPPL.Syntax R
open import DPPL.SmallStep R
open import DPPL.Properties.SmallStep R

open import Lib.Prelude hiding (_*_)
open import Lib.Data.Vector
open import Lib.LocallyNameless.BindingSignature
open import Lib.Syntax.EvalCtx
open import Lib.Syntax.Substitution

open import Data.Nat.Base using (Nat-is-set)

open Reals R
open Interval R
open ListSyntax

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
    Diff (_ , IsValue-is-prop Hv₀ Hv₀' i) (_ , IsValue-is-prop Hv₁ Hv₁' i) .fst
  →ᵈ-deterministic (esolve Hv₀ Hv₁ Hv₂) (esolve Hv₀' Hv₁' Hv₂') i =
    Solve
      (_ , IsValue-is-prop Hv₀ Hv₀' i)
      (_ , IsValue-is-prop Hv₁ Hv₁' i)
      (_ , IsValue-is-prop Hv₂ Hv₂' i)
      .fst


  DetCtx-cannot-step :
    {E : Tm → Tm}
    {t u : Tm}
    (_ : DetCtx E)
    (_ : ¬ IsValue t)
    → ---------------
    ¬ E t →ᵈ u

  DetCtx-cannot-step (ectx {j = j} _) Ht (eapp Heq Hv) with fin-view j
  ... | zero                         = Ht (subst IsValue (sym Heq) vlam)
  ... | suc i with zero ← fin-view i = Ht Hv
  DetCtx-cannot-step (ectx {j = j} _) Ht (eprim Heq) with zero ← fin-view j =
    Ht (subst IsValue (sym Heq) (vtup (λ _ → vreal)))
  DetCtx-cannot-step (ectx {j = j} _) Ht (eproj i Heq Hvs) with zero ← fin-view j =
    Ht (subst IsValue (sym Heq) (vtup Hvs))
  DetCtx-cannot-step (ectx {j = j} _) Ht (eif Heq) with zero ← fin-view j =
    Ht (subst IsValue (sym Heq) vreal)
  DetCtx-cannot-step (ectx {j = j} _) Ht (ediff Hv₀ Hv₁) with fin-view j
  ... | zero                         = Ht Hv₀
  ... | suc i with zero ← fin-view i = Ht Hv₁
  DetCtx-cannot-step (ectx {j = j} _) Ht (esolve Hv₀ Hv₁ Hv₂) with fin-view j
  ... | zero = Ht Hv₀
  ... | suc i with fin-view i
  ... | zero                         = Ht Hv₁
  ... | suc i with zero ← fin-view i = Ht Hv₂

  →det-deterministic : Deterministic _→det_
  →det-deterministic =
    CongCls-deterministic →ᵈ-deterministic
      (λ Hctx1 Hctx2 Ht Hu Heq →
        EvalCtx-unique IsValue Hctx1 Hctx2
          (λ Hv → value-cannot-step-det Hv Ht)
          (λ Hv → value-cannot-step-det Hv Hu)
          Heq)
      (λ Hctx Ht →
        DetCtx-cannot-step Hctx
          (λ Hv → value-cannot-step-det Hv Ht))


  →ʳ-deterministic : Deterministic _→ʳ_
  →ʳ-deterministic (edet Hstep) (edet Hstep') =
    ap (λ t → t , _) (→ᵈ-deterministic Hstep Hstep')
  →ʳ-deterministic (eweight Heq) (eweight Heq') =
    ap (λ r → _ , (if is-pos r then r * _ else _) , _) (real-inj (sym Heq ∙ Heq'))
  →ʳ-deterministic euniform euniform                   = refl
  →ʳ-deterministic (esample {w = w} {s = s} Heq Hv) (esample Heq' Hv') =
    ap (λ v → Infer v _ .fst , w , s) (op-inj' (sym Heq ∙ Heq') $ₚ _ ,ₚ prop!)

  RndCtx-unique :
    {E E' : Tm × ℝ × List 𝕀 → Tm × ℝ × List 𝕀}
    {t u : Tm × ℝ × List 𝕀}
    (_ : RndCtx E)
    (_ : RndCtx E')
    (_ : ¬ IsValue (t .fst))
    (_ : ¬ IsValue (u .fst))
    → -------------------------
    E t ≡ E' u → E ≡ E' × t ≡ u

  RndCtx-unique (E , Hctx , reflᵢ) (E' , Hctx' , reflᵢ) Ht Hu Heq
    with p , q ← EvalCtx-unique IsValue Hctx Hctx' Ht Hu (ap fst Heq) =
    ap ×-map₁ p , (q ,ₚ ap snd Heq)

  RndCtx-cannot-step :
    {E : Tm × ℝ × List 𝕀 → Tm × ℝ × List 𝕀}
    {t u : Tm × ℝ × List 𝕀}
    (_ : RndCtx E)
    (_ : ¬ IsValue (t .fst))
    → ---------------------
    ¬ E t →ʳ u

  RndCtx-cannot-step {E} {t} (_ , ectx Hvs , reflᵢ) Ht (edet Hstep) =
    DetCtx-cannot-step (ectx Hvs) Ht Hstep
  RndCtx-cannot-step {E} {t} (_ , ectx {j = j} Hvs , reflᵢ) Ht (eweight Heq)
    with zero ← fin-view j = Ht (subst IsValue (sym Heq) vreal)
  RndCtx-cannot-step {E} {t} (_ , ectx {j = j} Hvs , reflᵢ) Ht (esample Heq Hv)
    with zero ← fin-view j = Ht (subst IsValue (sym Heq) (vinfer Hv))

  →rnd-deterministic : Deterministic _→rnd_
  →rnd-deterministic =
    CongCls-deterministic →ʳ-deterministic
      (λ Hctx1 Hctx2 Ht Hu Heq →
        RndCtx-unique Hctx1 Hctx2
          (λ Hv → value-cannot-step-rnd Hv Ht)
          (λ Hv → value-cannot-step-rnd Hv Hu)
          Heq)
      (λ Hctx Ht →
        RndCtx-cannot-step Hctx
          (λ Hv → value-cannot-step-rnd Hv Ht))
