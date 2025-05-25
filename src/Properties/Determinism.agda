open import Lib.Reals

module Properties.Determinism (R : Reals₀) where

open Reals R hiding (refl)
open Interval R

open import Lib.Prelude
open import Lib.FunExt
open import Lib.BindingSignature
open import Lib.EvalCtx

open import Syntax R
open import SmallStep R
open import Properties.SmallStep R
open import Properties.Util

open import Data.Fin.Properties using (<-cmp)
open import Data.Product using (map₁)
open import Data.Product.Properties using (,-injective)
open import Data.Vec.Functional using (updateAt)
open import Data.Vec.Functional.Properties using (updateAt-updates ; updateAt-minimal ; updateAt-updateAt)
open import Relation.Binary.Rewriting using (Deterministic)
open import Relation.Binary using (Tri ; tri< ; tri≈ ; tri>)

module _ (Ass : EvalAssumptions) where
  open EvalAssumptions Ass
  open Eval Ass
  open Step Ass

  →ᵈ-deterministic : Deterministic _≡_ _→ᵈ_

  →ᵈ-deterministic (eapp Heq Hv) (eapp Heq′ Hv′)
    rewrite Heq with refl ← Heq′ = refl
  →ᵈ-deterministic (eprim {ϕ} Heq) (eprim Heq′) rewrite Heq =
    ap (real ∘ PrimEv ϕ) $ vmap-injective real (λ {refl → refl}) Heq′
  →ᵈ-deterministic (eproj _ Heq _) (eproj _ Heq′ _)
    rewrite Heq with refl ← Heq′ = refl
  →ᵈ-deterministic (eif Heq) (eif Heq′)
    rewrite Heq with refl ← Heq′ = refl
  →ᵈ-deterministic (ediff v₁ v₂) (ediff v₁′ v₂′) with
    refl ← value-irrelevant v₁ v₁′ | refl ← value-irrelevant v₂ v₂′ = refl
  →ᵈ-deterministic (esolve v₁ v₂ v₃) (esolve v₁′ v₂′ v₃′)
    with refl ← value-irrelevant v₁ v₁′
       | refl ← value-irrelevant v₂ v₂′
       | refl ← value-irrelevant v₃ v₃′ = refl

  DetCtx-unique :
    {E E′ : Term → Term}
    {t u : Term}
    (_ : DetCtx E)
    (_ : DetCtx E′)
    (_ : ¬ IsValue t)
    (_ : ¬ IsValue u)
    → -------------------------
    E t ≡ E′ u → E ≡ E′ × t ≡ u

  DetCtx-unique {t = t} {u = u} (ectx {o} {i} {ts} Hvs) (ectx {j = j} {ts′} Hvs′) Ht Hu Heq
    with refl , Heq′ ← op-injective Heq with <-cmp i j
  ... | tri< H< H≢ _ =
        𝟘e $ Ht (subst IsValue Heqt (Hvs′ i H<))
    where
    H≢′ : ¬ ord {o = o} i ≡ ord {o = o} j
    H≢′ = H≢ ∘ inj {o = o}
    Heqt = proof                                    ts′ _
           ≡[ symm $ updateAt-minimal _ _ ts′ H≢′ ] updateAt ts′ _ (const u) _
           ≡[ symm $ ap (_$ _) Heq′ ]               updateAt ts  _ (const t) _
           ≡[ updateAt-updates _ ts ]               t
           qed
  ... | tri> _ H≢ H> =
        𝟘e $ Hu (subst IsValue Heqt (Hvs j H>))
    where
    H≢′ : ¬ ord {o = o} j ≡ ord {o = o} i
    H≢′ = H≢ ∘ inj {o = o} ∘ symm
    Heqt = proof                                   ts _
           ≡[ symm $ updateAt-minimal _ _ ts H≢′ ] updateAt ts  _ (const t) _
           ≡[ ap (_$ _) Heq′ ]                     updateAt ts′ _ (const u) _
           ≡[ updateAt-updates _ ts′ ]             u
           qed
  ... | tri≈ _ refl _ = Heq₁ , Heq₂
    where
    Heq₁ = funext λ s → ap (op ∘ (o ,_)) $
           proof                                       updateAt ts _ (const s)
           ≡[ symm $ funext $ updateAt-updateAt _ ts ] updateAt (updateAt ts _ (const t)) _ (const s)
           ≡[ ap (λ xs → updateAt xs _ _) $ Heq′ ]     updateAt (updateAt ts′ _ (const u)) _ (const s)
           ≡[ funext $ updateAt-updateAt _ ts′ ]       updateAt ts′ _ (const s)
           qed
    Heq₂ = proof                             t
           ≡[ symm $ updateAt-updates _ ts ] updateAt ts  _ (const t) _
           ≡[ ap (_$ _) Heq′ ]               updateAt ts′ _ (const u) _
           ≡[ updateAt-updates _ ts′ ]       u
           qed

  DetCtx-cannot-step :
    {E : Term → Term}
    {t u : Term}
    (_ : DetCtx E)
    (_ : ¬ IsValue t)
    → ---------------
    ¬ E t →ᵈ u

  DetCtx-cannot-step (ectx {j = ₀} _) Ht (eapp refl _) = Ht vabs
  DetCtx-cannot-step (ectx {j = ₁} _) Ht (eapp _ Hv) = Ht Hv
  DetCtx-cannot-step {t = t} (ectx {j = j} {ts} _) Ht (eprim {rs = rs} Heq) =
    Ht (subst IsValue Heq′ (vreal {rs j}))
    where Heq′ = proof                      real (rs j)
                 ≡[ symm $ ap (_$ j) Heq ]  updateAt ts j (const t) j
                 ≡[ updateAt-updates j ts ] t
                 qed
  DetCtx-cannot-step (ectx {j = ₀} _) Ht (eproj i refl Hvs) = Ht (vtup Hvs)
  DetCtx-cannot-step (ectx {j = ₀} _) Ht (eif refl) = Ht vreal
  DetCtx-cannot-step (ectx {j = ₀} _) Ht (ediff v₀ v₁) = Ht v₀
  DetCtx-cannot-step (ectx {j = ₁} _) Ht (ediff v₀ v₁) = Ht v₁
  DetCtx-cannot-step (ectx {j = ₀} _) Ht (esolve v₀ v₁ v₂) = Ht v₀
  DetCtx-cannot-step (ectx {j = ₁} _) Ht (esolve v₀ v₁ v₂) = Ht v₁
  DetCtx-cannot-step (ectx {j = ₂} _) Ht (esolve v₀ v₁ v₂) = Ht v₂

  →det-deterministic : Deterministic _≡_ _→det_
  →det-deterministic =
    CongCls-deterministic →ᵈ-deterministic
      (λ Hctx1 Hctx2 Ht Hu Heq →
        DetCtx-unique Hctx1 Hctx2
          (λ Hv → value-cannot-step-det Hv Ht)
          (λ Hv → value-cannot-step-det Hv Hu)
          Heq)
      (λ Hctx Ht →
        DetCtx-cannot-step Hctx
          (λ Hv → value-cannot-step-det Hv Ht))


  →ʳ-deterministic : Deterministic _≡_ _→ʳ_

  →ʳ-deterministic (edet Hstep) (edet Hstep′) =
    ap (λ t → t , _) (→ᵈ-deterministic Hstep Hstep′)
  →ʳ-deterministic (eweight Heq) (eweight Heq′)
    rewrite Heq with refl ← Heq′ = refl
  →ʳ-deterministic (eassumedist {D = D} Heq) (eassumedist Heq′)
    rewrite Heq with refl , Hmap ← op-injective Heq′ =
    ap (λ rs → Sample D rs _ .π₁ , _) $ vmap-injective real (λ {refl → refl}) Hmap
  →ʳ-deterministic (eassumeinfer Heq Hv) (eassumeinfer Heq′ Hv′)
    rewrite Heq with refl ← Heq′ with refl ← value-irrelevant Hv Hv′ = refl
  →ʳ-deterministic (eassumedist Heq) (eassumeinfer Heq′ _)
    rewrite Heq with () ← Heq′
  →ʳ-deterministic (eassumeinfer Heq _) (eassumedist Heq′)
    rewrite Heq with () ← Heq′

  RndCtx-unique :
    {E E′ : Term × ℝ × List 𝕀 → Term × ℝ × List 𝕀}
    {t u : Term × ℝ × List 𝕀}
    (_ : RndCtx E)
    (_ : RndCtx E′)
    (_ : ¬ IsValue (t .π₁))
    (_ : ¬ IsValue (u .π₁))
    → -------------------------
    E t ≡ E′ u → E ≡ E′ × t ≡ u

  RndCtx-unique (E , Hctx , refl) (E′ , Hctx′ , refl) Ht Hu Heq
    with Heq′ , refl ← ,-injective Heq
    with refl , refl ← DetCtx-unique Hctx Hctx′ Ht Hu Heq′ = refl , refl

  RndCtx-cannot-step :
    {E : Term × ℝ × List 𝕀 → Term × ℝ × List 𝕀}
    {t u : Term × ℝ × List 𝕀}
    (_ : RndCtx E)
    (_ : ¬ IsValue (t .π₁))
    → ---------------------
    ¬ E t →ʳ u

  RndCtx-cannot-step (_ , ectx Hvs , refl) Ht (edet Hstep) =
    DetCtx-cannot-step (ectx Hvs) Ht Hstep
  RndCtx-cannot-step (_ , ectx {j = ₀} _ , refl) Ht (eweight refl) = Ht vreal
  RndCtx-cannot-step (_ , ectx {j = ₀} _ , refl) Ht (eassumedist refl) =
    Ht (vdist (λ _ → vreal))
  RndCtx-cannot-step (_ , ectx {j = ₀} _ , refl) Ht (eassumeinfer refl v) =
    Ht (vinfer v)

  →rnd-deterministic : Deterministic _≡_ _→rnd_
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
