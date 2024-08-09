module Properties.Determinism (ℝ 𝕀 : Set) where

open import Lib.Prelude
open import Lib.FunExt
open import Lib.BindingSignature
open import Lib.EvalCtx

open import Syntax ℝ
open import SmallStep ℝ 𝕀
open import Properties.SmallStep ℝ 𝕀
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
  →ᵈ-deterministic (eexpectdist {D} Heq) (eexpectdist Heq′)
    rewrite Heq with refl , Hmap ← op-injective Heq′ =
    ap (real ∘ Expect ∘ Sample D) $ vmap-injective real (λ {refl → refl}) Hmap
  →ᵈ-deterministic (eexpectinfer Heq Hv) (eexpectinfer Heq′ Hv′)
    rewrite Heq with refl ← Heq′ with refl ← value-irrelevant Hv Hv′ = refl
  →ᵈ-deterministic (eexpectdist Heq) (eexpectinfer Heq′ _)
    rewrite Heq with () ← Heq′
  →ᵈ-deterministic (eexpectinfer Heq _) (eexpectdist Heq′)
    rewrite Heq with () ← Heq′

  DetCtx-unique
    : ∀ {E E′ t t′ u u′}
    → DetCtx E
    → DetCtx E′
    → t →det t′
    → u →det u′
    → E t ≡ E′ u
    → --------------
      E ≡ E′ × t ≡ u

  DetCtx-unique {t = t} {u = u} (ectx {o} {i} {ts} Hvs) (ectx {j = j} {ts′} Hvs′) Ht Hu Heq
    with refl , Heq′ ← op-injective Heq with <-cmp i j
  ... | tri< H< H≢ _ =
        𝟘e $ value-cannot-step-det (subst Value Heqt (Hvs′ i H<)) Ht
    where
    H≢′ : ¬ ord {o = o} i ≡ ord {o = o} j
    H≢′ = H≢ ∘ inj {o = o}
    Heqt = proof                                    ts′ _
           ≡[ symm $ updateAt-minimal _ _ ts′ H≢′ ] updateAt ts′ _ (const u) _
           ≡[ symm $ ap (_$ _) Heq′ ]               updateAt ts  _ (const t) _
           ≡[ updateAt-updates _ ts ]               t
           qed
  ... | tri> _ H≢ H> =
        𝟘e $ value-cannot-step-det (subst Value Heqt (Hvs j H>)) Hu
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

  DetCtx-cannot-step
    : ∀ {E t t′ u}
    → DetCtx E
    → t →det t′
    → ----------
      ¬ E t →ᵈ u

  DetCtx-cannot-step (ectx {j = ₀} _) Ht (eapp refl _) =
    value-cannot-step-det vabs Ht
  DetCtx-cannot-step (ectx {j = ₁} _) Ht (eapp _ Hv) =
    value-cannot-step-det Hv Ht
  DetCtx-cannot-step {t = t} (ectx {j = j} {ts} _) Ht (eprim {rs = rs} Heq) =
    value-cannot-step-det (vreal {rs j}) (subst (_→det _) Heq′ Ht)
    where Heq′ = proof                             t
                 ≡[ symm $ updateAt-updates j ts ] updateAt ts j (const t) j
                 ≡[ ap (_$ j) Heq ]                real (rs j)
                 qed
  DetCtx-cannot-step (ectx {j = ₀} _) Ht (eproj i refl Hvs) =
    value-cannot-step-det (vtup Hvs) Ht
  DetCtx-cannot-step (ectx {j = ₀} _) Ht (eif refl) =
    value-cannot-step-det vreal Ht
  DetCtx-cannot-step (ectx {j = ₀} _) Ht (ediff v₀ v₁) =
    value-cannot-step-det v₀ Ht
  DetCtx-cannot-step (ectx {j = ₁} _) Ht (ediff v₀ v₁) =
    value-cannot-step-det v₁ Ht
  DetCtx-cannot-step (ectx {j = ₀} _) Ht (esolve v₀ v₁ v₂) =
    value-cannot-step-det v₀ Ht
  DetCtx-cannot-step (ectx {j = ₁} _) Ht (esolve v₀ v₁ v₂) =
    value-cannot-step-det v₁ Ht
  DetCtx-cannot-step (ectx {j = ₂} _) Ht (esolve v₀ v₁ v₂) =
    value-cannot-step-det v₂ Ht
  DetCtx-cannot-step (ectx {j = ₀} _) Ht (eexpectdist refl) =
    value-cannot-step-det (vdist (λ _ → vreal)) Ht
  DetCtx-cannot-step (ectx {j = ₀} _) Ht (eexpectinfer refl v) =
    value-cannot-step-det (vinfer v) Ht

  →det-deterministic : Deterministic _≡_ _→det_
  →det-deterministic =
    CongCls-deterministic →ᵈ-deterministic DetCtx-unique DetCtx-cannot-step


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

  -- RndCtx-unique
  --   : ∀ {E E′ t t′ u u′}
  --   → RndCtx E
  --   → RndCtx E′
  --   → t →rnd t′
  --   → u →rnd u′
  --   → E t ≡ E′ u
  --   → --------------
  --     E ≡ E′ × t ≡ u

  -- RndCtx-unique (E , Hctx , refl) (E′ , Hctx′ , refl) Ht Hu Heq
  --   with Heq′ , refl ← ,-injective Heq
  --   with refl , refl ← DetCtx-unique Hctx Hctx′ {!!} {!!} Heq′ = refl , refl

  -- RndCtx-cannot-step
  --   : ∀ {E t u}
  --   → RndCtx E
  --   → ----------
  --     ¬ E t →ʳ u

  -- RndCtx-cannot-step {E₀} {t} (E , Hctx , Heq) Hstep
  --   with Et ← E₀ t in HEt | Hstep
  -- ... | edet Hstep′
  --   with refl ← Heq | refl ← HEt
  --   with () ← DetCtx-cannot-step Hctx Hstep′
  -- ... | eweight Heq′ rewrite Heq′
  --   with refl ← Heq = {!!}
  -- ... | eassumedist x = {!!}
  -- ... | eassumeinfer x v = {!!}

  -- →rnd-deterministic : Deterministic _≡_ _→rnd_
  -- →rnd-deterministic =
  --   CongCls-deterministic →ʳ-deterministic RndCtx-unique RndCtx-cannot-step
