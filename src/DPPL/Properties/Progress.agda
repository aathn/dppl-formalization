open import Lib.Algebra.Reals

module DPPL.Properties.Progress (R : Reals₀) where

-- Proofs of progress for the DPPL semantics

open Reals R using (ℝ)
open Interval R using (𝕀)

open import DPPL.Syntax R
open import DPPL.Typing R
open import DPPL.SmallStep R
open import DPPL.Properties.SmallStep R
open import DPPL.Properties.Typing R

open import Lib.Prelude
open import Lib.Data.Fin
open import Lib.Data.Finset
open import Lib.Syntax.EvalCtx
open import Lib.Syntax.Env

open import Data.Finset.Base

open SyntaxVars
open ListSyntax
open EvalVars
open NatOrd

module Progress (Ax : EvalAssumptions) where
  open Eval Ax
  open Step Ax

  progress-det :
    ε ⊢ t :[ det ] T
    → --------------------------------
    IsValue t ⊎ Σ[ t' ∈ Tm ] t →det t'

  progress-det (tlam _)                = inl vlam
  progress-det treal                   = inl vreal
  progress-det (tvar H∈)               = absurd (¬mem-[] (env-sub→dom-sub H∈ _ hereₛ))
  progress-det (tapp Hty Hty₁)         = inr $ case (progress-det Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
    (inl Hv) → case (progress-det Hty₁) of λ where
      (inr (t' , Hstep)) → _ , cong-stepᵈ (Fin-cases (λ _ → Hv) λ _ ()) Hstep
      (inl Hv₁) →
        let _ , t , Heq = canonical-⇒ Hty Hv reflᵢ
        in  _ , estep (eapp Heq Hv₁)
  progress-det (tprim Hϕ Hty) = inr $ case (progress-det Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq , Hvs = canonical-tup Hty Hv reflᵢ
          Htys          = ttup-inv (subst (_ ⊢_:[ _ ] _) Heq Hty) reflᵢ
          Hreals i      = canonical-real (Htys i) (Hvs i) reflᵢ .snd
      in _ , estep (eprim (Heq ∙ ap (tup _ ▸_) (funext Hreals)))
  progress-det (ttup Htys) with Fin-search-⊎ (progress-det ∘ Htys)
  ... | inr (j , (t' , Hstep) , Hvs) = inr $ _ , cong-stepᵈ Hvs Hstep
  ... | inl Hvs                      = inl $ vtup Hvs
  progress-det (tproj i Hty) = inr $ case (progress-det Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq , Hvs = canonical-tup Hty Hv reflᵢ
      in  _ , estep (eproj i Heq Hvs)
  progress-det (tif Hty Hty₁ Hty₂ _) = inr $ case (progress-det Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ {n = fzero} (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq = canonical-real Hty Hv reflᵢ
      in  _ , estep (eif Heq)
  progress-det (tinfer Hty) with progress-det Hty
  ... | inr (t' , Hstep) = inr $ _ , cong-stepᵈ (λ _ ()) Hstep
  ... | inl Hv           = inl $ vinfer Hv
  progress-det (tdiff Hty Hty₁ Hty₂ _) = inr $ case (progress-det Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
    (inl Hv) → case (progress-det Hty₁) of λ where
      (inr (t' , Hstep)) → _ , cong-stepᵈ (Fin-cases (λ _ → Hv) λ _ ()) Hstep
      (inl Hv₁) → case (progress-det Hty₂) of λ where
        (inr (t' , Hstep)) →
          _ , cong-stepᵈ (Fin-cases (λ _ → Hv) $ Fin-cases (λ _ → Hv₁) λ _ ()) Hstep
        (inl Hv₂) → _ , estep (ediff Hv Hv₁ Hv₂)
  progress-det (tsolve Hty Hty₁ Hty₂ _) = inr $ case (progress-det Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
    (inl Hv) → case (progress-det Hty₁) of λ where
      (inr (t' , Hstep)) → _ , cong-stepᵈ (Fin-cases (λ _ → Hv) λ _ ()) Hstep
      (inl Hv₁) → case (progress-det Hty₂) of λ where
        (inr (t' , Hstep)) →
          _ , cong-stepᵈ (Fin-cases (λ _ → Hv) $ Fin-cases (λ _ → Hv₁) λ _ ()) Hstep
        (inl Hv₂) → _ , estep (esolve Hv Hv₁ Hv₂)
  progress-det (tsub {e = det} Hty _ _) = progress-det Hty
  progress-det (tpromote {Γ} Hty _ H⊆)
    rewrite Id≃path.from (env-sub-dom-eq H⊆ ∈Ø-elim) = progress-det Hty


  progress-rnd :
    ε ⊢ t :[ rnd ] T
    → ---------------------------------------------------------------
    IsValue t ⊎ Σ[ tws' ∈ Tm × ℝ × List 𝕀 ] (t , w , p ∷ s) →rnd tws'

  progress-rnd (tapp Hty Hty₁) = inr $ case (progress-rnd Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
    (inl Hv) → case (progress-rnd Hty₁) of λ where
      (inr (t' , Hstep)) → _ , cong-stepʳ (Fin-cases (λ _ → Hv) λ _ ()) Hstep
      (inl Hv₁) →
        let _ , t , Heq = canonical-⇒ Hty Hv reflᵢ
        in  _ , estep (edet (eapp Heq Hv₁))
  progress-rnd (tprim x Hty) = inr $ case (progress-rnd Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq , Hvs = canonical-tup Hty Hv reflᵢ
          Htys          = ttup-inv (subst (_ ⊢_:[ _ ] _) Heq Hty) reflᵢ
          Hreals i      = canonical-real (Htys i) (Hvs i) reflᵢ .snd
      in _ , estep (edet (eprim (Heq ∙ ap (tup _ ▸_) (funext Hreals))))
  progress-rnd (ttup Htys) with Fin-search-⊎ (progress-rnd ∘ Htys)
  ... | inr (j , (t' , Hstep) , Hvs) = inr $ _ , cong-stepʳ Hvs Hstep
  ... | inl Hvs                      = inl $ vtup Hvs
  progress-rnd (tproj i Hty) = inr $ case (progress-rnd Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq , Hvs = canonical-tup Hty Hv reflᵢ
      in  _ , estep (edet (eproj i Heq Hvs))
  progress-rnd (tif Hty Hty₁ Hty₂ _) = inr $ case (progress-rnd Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepʳ {n = fzero} (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq = canonical-real Hty Hv reflᵢ
      in  _ , estep (edet (eif Heq))
  progress-rnd tuniform = inr $ _ , estep euniform
  progress-rnd (tsample Hty) = inr $ case (progress-rnd Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq , Hv = canonical-dist Hty Hv reflᵢ
      in  _ , estep (esample Heq Hv)
  progress-rnd (tweight Hty) = inr $ case (progress-rnd Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
    (inl Hv) →
      let _ , Heq = canonical-real Hty Hv reflᵢ
      in  _ , estep (eweight Heq)
  progress-rnd (tinfer Hty) with progress-rnd Hty
  ... | inr (t' , Hstep) = inr $ _ , cong-stepʳ (λ _ ()) Hstep
  ... | inl Hv           = inl $ vinfer Hv
  progress-rnd (tdiff Hty Hty₁ Hty₂ _) = inr $ case (progress-rnd Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
    (inl Hv) → case (progress-rnd Hty₁) of λ where
      (inr (t' , Hstep)) → _ , cong-stepʳ (Fin-cases (λ _ → Hv) λ _ ()) Hstep
      (inl Hv₁) → case (progress-rnd Hty₂) of λ where
        (inr (t' , Hstep)) →
          _ , cong-stepʳ (Fin-cases (λ _ → Hv) $ Fin-cases (λ _ → Hv₁) λ _ ()) Hstep
        (inl Hv₂) → _ , estep (edet (ediff Hv Hv₁ Hv₂))
  progress-rnd (tsolve Hty Hty₁ Hty₂ _) = inr $ case (progress-rnd Hty) of λ where
    (inr (t' , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
    (inl Hv) → case (progress-rnd Hty₁) of λ where
      (inr (t' , Hstep)) → _ , cong-stepʳ (Fin-cases (λ _ → Hv) λ _ ()) Hstep
      (inl Hv₁) → case (progress-rnd Hty₂) of λ where
        (inr (t' , Hstep)) →
          _ , cong-stepʳ (Fin-cases (λ _ → Hv) $ Fin-cases (λ _ → Hv₁) λ _ ()) Hstep
        (inl Hv₂) → _ , estep (edet (esolve Hv Hv₁ Hv₂))
  progress-rnd (tsub {e = rnd} Hty _ _) = progress-rnd Hty
  progress-rnd (tsub {e = det} Hty _ _) with progress-det Hty
  ... | inr (_ , Hstep) = inr $ _ , →det⊆→rnd Hstep
  ... | inl Hv          = inl Hv
  progress-rnd (tpromote {Γ} Hty _ H⊆)
    rewrite Id≃path.from (env-sub-dom-eq H⊆ ∈Ø-elim) = progress-rnd Hty
