module Properties.Determinism (ℝ : Set) where

open import Lib.Prelude

open import Function using (_$_)

open import Syntax ℝ
open import SmallStep ℝ
open import Properties.Util

module _ (Ass : EvalAssumptions) where
  open Eval Ass
  open EvalAssumptions Ass

  dist-inv
    : ∀ {D D′ ts ts′}
    → dist D ts ≡ dist D′ ts′
    → ----------------------------------------------------------
      ∑ Heq ∶ D ≡ D′ , subst (Vector Term ∘ DistAr) Heq ts ≡ ts′

  dist-inv = λ { refl → refl , refl }


  →ᵈ-deterministic
    : ∀ {t s u}
    → t →ᵈ s
    → t →ᵈ u
    → ------
      s ≡ u
   
  →ᵈ-deterministic (eapp Heq Hv) (eapp Heq′ Hv′)
    rewrite Heq with refl ← Heq′ = refl
  →ᵈ-deterministic (eprim {ϕ} Heq) (eprim Heq′) rewrite Heq =
    ap (real ∘ PrimEv ϕ) $ vmap-injective real (λ {refl → refl}) Heq′
  →ᵈ-deterministic (eproj _ Heq _) (eproj _ Heq′ _)
    rewrite Heq with refl ← Heq′ = refl
  →ᵈ-deterministic (eif Heq) (eif Heq′)
    rewrite Heq with refl ← Heq′ = refl
  →ᵈ-deterministic (ediff _ _) (ediff _ _) = refl
  →ᵈ-deterministic (esolve _ _ _) (esolve _ _ _) = refl
  →ᵈ-deterministic (eexpectdist {D} Heq) (eexpectdist Heq′)
    rewrite Heq with refl , Hmap ← dist-inv Heq′ =
    ap (real ∘ ExpectDist D) $ vmap-injective real (λ {refl → refl}) Hmap
  →ᵈ-deterministic (eexpectinfer Heq Hv) (eexpectinfer Heq′ Hv′)
    rewrite Heq with refl ← Heq′ = refl
  →ᵈ-deterministic (eexpectdist Heq) (eexpectinfer Heq′ _)
    rewrite Heq with () ← Heq′
  →ᵈ-deterministic (eexpectinfer Heq _) (eexpectdist Heq′)
    rewrite Heq with () ← Heq′

  →ʳ-deterministic
    : ∀ {t s u}
    → t →ʳ s
    → t →ʳ u
    → ------
      s ≡ u

  →ʳ-deterministic (edet Hstep) (edet Hstep′) =
    ap (λ t → t , _) (→ᵈ-deterministic Hstep Hstep′)
  →ʳ-deterministic (eweight Heq) (eweight Heq′)
    rewrite Heq with refl ← Heq′ = refl
  →ʳ-deterministic (eassumedist {D = D} Heq) (eassumedist Heq′)
    rewrite Heq with refl , Hmap ← dist-inv Heq′ =
    ap (λ rs → AssumeDist D rs _ , _) $ vmap-injective real (λ {refl → refl}) Hmap
  →ʳ-deterministic (eassumeinfer Heq _) (eassumeinfer Heq′ _)
    rewrite Heq with refl ← Heq′ = refl
  →ʳ-deterministic (eassumedist Heq) (eassumeinfer Heq′ _)
    rewrite Heq with () ← Heq′
  →ʳ-deterministic (eassumeinfer Heq _) (eassumedist Heq′)
    rewrite Heq with () ← Heq′

-- CongCls-deterministic
