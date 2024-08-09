module Properties.Progress (ℝ 𝕀 : Set) where

-- Proofs of progress for the DPPL semantics

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ 𝕀
open import Properties.SmallStep ℝ 𝕀
open import Properties.Util

open import Lib.Prelude
open import Lib.FunExt
open import Lib.EvalCtx

open import Data.List.Relation.Binary.Sublist.Propositional using ([])
open import Data.Product using (∃-syntax)
open import Data.Vec.Functional using (map)

module Progress (Ass : EvalAssumptions) where
  open Eval Ass
  open Step Ass

  progress-det
    : ∀ {t T}
    → [] ⊢ t :[ det ] T
    → ------------------------------
      Value t ⊎ ∃[ t′ ] t →det t′

  progress-det (tabs _) = ι₁ vabs
  progress-det treal    = ι₁ vreal
  progress-det (tapp Htype Htype₁) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₂ (t′ , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (progress-det Htype₁) λ
        { (ι₂ (t′ , Hstep)) → _ , cong-stepᵈ (λ {₀ (+1≤ 0≤) → Hv}) Hstep
        ; (ι₁ Hv₁) → case (canonical-⇒ Htype Hv refl) λ
          { (_ , t , Heq) → _ , estep (eapp Heq Hv₁) }
        }
      }
  progress-det (tprim {ts = ts} Hϕ Htypes _) =
    ι₂ $ case (all-⊎ (progress-det ∘ Htypes)) λ
      { (ι₁ Hvs) →
        let Hreals : ts ≡ map real _
            Hreals = funext λ i → π₂ $ canonical-real (Htypes i) (Hvs i) refl
        in _ , estep (eprim Hreals)
      ; (ι₂ (j , (t′ , Hstep) , Hvs)) → _ , cong-stepᵈ Hvs Hstep
      }
  progress-det (ttup Htypes _) =
    case (all-⊎ (progress-det ∘ Htypes)) λ
      { (ι₂ (j , (t′ , Hstep) , Hvs)) → ι₂ $ _ , cong-stepᵈ Hvs Hstep
      ; (ι₁ Hvs)                      → ι₁ $ vtup Hvs
      }
  progress-det (tproj i Htype) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₂ (t′ , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (canonical-tup Htype Hv refl) λ
        { (ts , Heq , Hvs) → _ , estep (eproj i Heq Hvs) }
      }
  progress-det (tif Htype Htype₁ Htype₂) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₂ (t′ , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (canonical-real Htype Hv refl) λ
        { (r , Heq) → _ , estep (eif Heq) }
      }
  progress-det (tdiff _ Htype Htype₁) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₂ (t′ , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (progress-det Htype₁) λ
        { (ι₁ Hv₁) → _ , estep (ediff Hv Hv₁)
        ; (ι₂ (t′ , Hstep)) →
          _ , cong-stepᵈ (λ {₀ (+1≤ 0≤) → Hv}) Hstep
        }
      }
  progress-det (tsolve Htype Htype₁ Htype₂) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₂ (t′ , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (progress-det Htype₁) λ
        { (ι₂ (t′ , Hstep)) → _ , cong-stepᵈ (λ {₀ (+1≤ 0≤) → Hv}) Hstep
        ; (ι₁ Hv₁) → case (progress-det Htype₂) λ
          { (ι₂ (t′ , Hstep)) →
              _ , cong-stepᵈ
                    (λ {₀ (+1≤ 0≤) → Hv ; ₁ (+1≤ (+1≤ 0≤)) → Hv₁})
                    Hstep
          ; (ι₁ Hv₂) → _ , estep (esolve Hv Hv₁ Hv₂)
          }
        }
      }
  progress-det (tdist _ Htypes _) =
    case (all-⊎ (progress-det ∘ Htypes)) λ
      { (ι₂ (j , (t′ , Hstep) , Hvs)) → ι₂ $ _ , cong-stepᵈ Hvs Hstep
      ; (ι₁ Hvs)                      → ι₁ $ vdist Hvs
      }
  progress-det (texpect Htype) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₂ (t′ , Hstep)) → _ , cong-stepᵈ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (canonical-dist Htype Hv refl) λ
        { (ι₁ (D , ts , Heq)) → _ , estep (eexpectdist Heq)
        ; (ι₂ (v , Heq , Hv)) → _ , estep (eexpectinfer Heq Hv)
        }
      }
  progress-det (tinfer Htype) =
    case (progress-det Htype) λ
      { (ι₂ (t′ , Hstep)) → ι₂ $ _ , cong-stepᵈ (λ _ ()) Hstep
      ; (ι₁ Hv)           → ι₁ $ vinfer Hv
      }
  progress-det (tweaken Htype [] _) = progress-det Htype
  progress-det (tsub Htype 0≤ _)    = progress-det Htype
  progress-det (tpromote {[]} Htype H≤) = progress-det Htype


  progress-rnd
    : ∀ {t T w p s}
    → [] ⊢ t :[ rnd ] T
    → -------------------------------------------------
      Value t ⊎ ∑ tws′ ∶ _ , (t , w , p :: s) →rnd tws′

  progress-rnd (tapp Htype Htype₁) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (progress-rnd Htype₁) λ
        { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ {₀ (+1≤ 0≤) → Hv}) Hstep
        ; (ι₁ Hv₁) → case (canonical-⇒ Htype Hv refl) λ
          { (_ , t , Heq) → _ , estep (edet (eapp Heq Hv₁)) }
        }
      }
  progress-rnd (tprim {ts = ts} Hϕ Htypes _) =
    ι₂ $ case (all-⊎ (progress-rnd ∘ Htypes)) λ
      { (ι₂ (j , (_ , Hstep) , Hvs)) → _ , cong-stepʳ Hvs Hstep
      ; (ι₁ Hvs) →
        let Hreals : ts ≡ map real _
            Hreals = funext λ i → π₂ $ canonical-real (Htypes i) (Hvs i) refl
        in _ , estep (edet (eprim Hreals))
      }
  progress-rnd (ttup Htypes _) =
    case (all-⊎ (progress-rnd ∘ Htypes)) λ
      { (ι₂ (j , (_ , Hstep) , Hvs)) → ι₂ $ _ , cong-stepʳ Hvs Hstep
      ; (ι₁ Hvs)                     → ι₁ $ vtup Hvs
      }
  progress-rnd (tproj i Htype) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (canonical-tup Htype Hv refl) λ
        { (ts , Heq , Hvs) → _ , estep (edet (eproj i Heq Hvs)) }
      }
  progress-rnd (tif Htype Htype₁ Htype₂) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (canonical-real Htype Hv refl) λ
        { (r , Heq) → _ , estep (edet (eif Heq)) }
      }
  progress-rnd (tdiff _ Htype Htype₁) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (progress-rnd Htype₁) λ
        { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ {₀ (+1≤ 0≤) → Hv}) Hstep
        ; (ι₁ Hv₁) → _ , estep (edet (ediff Hv Hv₁))
        }
      }
  progress-rnd (tsolve Htype Htype₁ Htype₂) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (progress-rnd Htype₁) λ
        { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ {₀ (+1≤ 0≤) → Hv}) Hstep
        ; (ι₁ Hv₁) → case (progress-rnd Htype₂) λ
          { (ι₂ (_ , Hstep)) →
            _ , cong-stepʳ
                  (λ {₀ (+1≤ 0≤) → Hv ; ₁ (+1≤ (+1≤ 0≤)) → Hv₁})
                  Hstep
          ; (ι₁ Hv₂) → _ , estep (edet (esolve Hv Hv₁ Hv₂))
          }
        }
      }
  progress-rnd (tdist _ Htypes _) =
    case (all-⊎ (progress-rnd ∘ Htypes)) λ
      { (ι₂ (j , (_ , Hstep) , Hvs)) → ι₂ $ _ , cong-stepʳ Hvs Hstep
      ; (ι₁ Hvs)                     → ι₁ $ vdist Hvs
      }
  progress-rnd (texpect Htype) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (canonical-dist Htype Hv refl) λ
        { (ι₁ (D , ts , Heq)) → _ , estep (edet (eexpectdist Heq))
        ; (ι₂ (v , Heq , Hv)) → _ , estep (edet (eexpectinfer Heq Hv))
        }
      }
  progress-rnd (tassume Htype) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (canonical-dist Htype Hv refl) λ
        { (ι₁ (D , ts , Heq)) → _ , estep (eassumedist Heq)
        ; (ι₂ (v , Heq , Hv)) → _ , estep (eassumeinfer Heq Hv)
        }
      }
  progress-rnd (tweight Htype) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₂ (_ , Hstep)) → _ , cong-stepʳ (λ _ ()) Hstep
      ; (ι₁ Hv) → case (canonical-real Htype Hv refl) λ
        { (r , Heq) → _ , estep (eweight Heq) }
      }
  progress-rnd (tinfer Htype) =
    case (progress-rnd Htype) λ
      { (ι₂ (_ , Hstep)) → ι₂ $ _ , cong-stepʳ (λ _ ()) Hstep
      ; (ι₁ Hv) → ι₁ $ vinfer Hv
      }
  progress-rnd (tweaken Htype [] _) = progress-rnd Htype
  progress-rnd (tsub Htype 0≤ _) =
    case (progress-det Htype) λ
      { (ι₁ Hv) → ι₁ Hv
      ; (ι₂ (_ , Hstep)) → ι₂ $ _ , →det⊆→rnd Hstep
      }
  progress-rnd (tsub Htype (+1≤ 0≤) _) = progress-rnd Htype
  progress-rnd (tpromote {[]} Htype H≤) = progress-rnd Htype
