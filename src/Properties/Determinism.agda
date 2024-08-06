module Properties.Determinism (ℝ 𝕀 : Set) where

open import Lib.Prelude
open import Lib.EvalCtx

open import Function using (_$_)

open import Syntax ℝ
open import SmallStep ℝ 𝕀
open import Properties.SmallStep ℝ 𝕀
open import Properties.Util

open import Data.Product using (map₁)
open import Data.Product.Properties using (,-injective)
open import Relation.Binary.Rewriting using (Deterministic)

module _ (Ass : EvalAssumptions) where
  open Eval Ass
  open EvalAssumptions Ass

  dist-inv
    : ∀ {D D′ ts ts′}
    → dist D ts ≡ dist D′ ts′
    → ----------------------------------------------------------
      ∑ Heq ∶ D ≡ D′ , subst (Vector Term ∘ DistAr) Heq ts ≡ ts′

  dist-inv = λ { refl → refl , refl }


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
    rewrite Heq with refl , Hmap ← dist-inv Heq′ =
    ap (real ∘ Expect ∘ Sample D) $ vmap-injective real (λ {refl → refl}) Hmap
  →ᵈ-deterministic (eexpectinfer Heq Hv) (eexpectinfer Heq′ Hv′)
    rewrite Heq with refl ← Heq′ with refl ← value-irrelevant Hv Hv′ = refl
  →ᵈ-deterministic (eexpectdist Heq) (eexpectinfer Heq′ _)
    rewrite Heq with () ← Heq′
  →ᵈ-deterministic (eexpectinfer Heq _) (eexpectdist Heq′)
    rewrite Heq with () ← Heq′

  DetCtx-unique
    : ∀ {E E′ t u}
    → DetCtx E
    → DetCtx E′
    → E t ≡ E′ u
    → --------------
      E ≡ E′ × t ≡ u

  DetCtx-unique = {!!}

  DetCtx-cannot-step
    : ∀ {E t u}
    → DetCtx E
    → ------------
      ¬ (E t →ᵈ u)

  DetCtx-cannot-step {t} (ectx {j = j} refl Hvs) Hstep = {!!}

  →det-deterministic : Deterministic _≡_ _→det_
  →det-deterministic =
    CongCls-deterministic →ᵈ-deterministic DetCtx-unique DetCtx-cannot-step


  →ʳ-deterministic : Deterministic _≡_ _→ʳ_

  →ʳ-deterministic (edet Hstep) (edet Hstep′) =
    ap (λ t → t , _) (→ᵈ-deterministic Hstep Hstep′)
  →ʳ-deterministic (eweight Heq) (eweight Heq′)
    rewrite Heq with refl ← Heq′ = refl
  →ʳ-deterministic (eassumedist {D = D} Heq) (eassumedist Heq′)
    rewrite Heq with refl , Hmap ← dist-inv Heq′ =
    ap (λ rs → Sample D rs _ .π₁ , _) $ vmap-injective real (λ {refl → refl}) Hmap
  →ʳ-deterministic (eassumeinfer Heq Hv) (eassumeinfer Heq′ Hv′)
    rewrite Heq with refl ← Heq′ with refl ← value-irrelevant Hv Hv′ = refl
  →ʳ-deterministic (eassumedist Heq) (eassumeinfer Heq′ _)
    rewrite Heq with () ← Heq′
  →ʳ-deterministic (eassumeinfer Heq _) (eassumedist Heq′)
    rewrite Heq with () ← Heq′

  RndCtx-unique
    : ∀ {E E′ t u}
    → RndCtx E
    → RndCtx E′
    → E t ≡ E′ u
    → --------------
      E ≡ E′ × t ≡ u

  RndCtx-unique (E , Hctx , refl) (E′ , Hctx′ , refl) Heq
    with Heq′ , refl ← ,-injective Heq
    with refl , refl ← DetCtx-unique Hctx Hctx′ Heq′ = refl , refl

  RndCtx-cannot-step
    : ∀ {E t u}
    → RndCtx E
    → ------------
      ¬ (E t →ʳ u)

  RndCtx-cannot-step {E₀} {t} (E , Hctx , Heq) Hstep
    with Et ← E₀ t in HEt | Hstep
  ... | edet Hstep′
    with refl ← Heq | refl ← HEt
    with () ← DetCtx-cannot-step Hctx Hstep′
  ... | eweight Heq′ rewrite Heq′
    with refl ← Heq = {!!}
  ... | eassumedist x = {!!}
  ... | eassumeinfer x v = {!!}

  →rnd-deterministic : Deterministic _≡_ _→rnd_
  →rnd-deterministic =
    CongCls-deterministic →ʳ-deterministic RndCtx-unique RndCtx-cannot-step
