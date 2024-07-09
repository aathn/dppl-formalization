module Properties.Progress (ℝ : Set) where

-- Proofs of progress for the DPPL semantics

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ
open import Properties.SmallStep ℝ
open import Properties.Util

open import Lib.Prelude
open import Lib.FunExt

open import Function using (_$_)
open import Data.List.Relation.Binary.Sublist.Propositional using ([])
open import Data.Product using (∃-syntax)
open import Data.Vec.Functional using (map)

module _ (Ass : EvalAssumptions) where
  open Eval Ass
  open Step Ass

  progress-det
    : ∀ {t T}
    → [] ⊢ t :[ det ] T
    → ------------------------------
      Value t ⊎ ∑ t′ ∶ _ , t →det t′

  progress-det (tabs _) = ι₁ vabs
  progress-det treal    = ι₁ vreal
  progress-det (tapp Htype Htype₁) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (progress-det Htype₁) λ
        { (ι₁ Hv₁) → case (canonical-⇒ Htype Hv refl) λ
          { (_ , t , Heq) → _ , estep (eapp Heq Hv₁) }
        ; (ι₂ (t′ , Hstep)) →
          _ , cong-step′ 1ꟳ refl (λ {0ꟳ (+1≤ 0≤) → Hv}) Hstep
        }
      ; (ι₂ (t′ , Hstep)) → _ , cong-step′ 0ꟳ refl (λ _ ()) Hstep
      }
  progress-det (tprim {ts = ts} Hϕ Htypes) =
    ι₂ $ case (all-⊎ (progress-det ∘ Htypes)) λ
      { (ι₁ Hvs) →
        let Hreals : ∃[ rs ] ts ≡ map real rs
            Hreals = _ , funext λ i → π₂ $ canonical-real (Htypes i) (Hvs i) refl
        in case Hreals λ { (_ , refl) → _ , estep eprim }
      ; (ι₂ (j , (t′ , Hstep) , Hvs)) → _ , cong-step′ j refl Hvs Hstep
      }
  progress-det (ttup Htypes) =
    case (all-⊎ (progress-det ∘ Htypes)) λ
      { (ι₁ Hvs)                      → ι₁ $ vtup Hvs
      ; (ι₂ (j , (t′ , Hstep) , Hvs)) → ι₂ $
        _ , cong-step′ j refl Hvs Hstep
      }
  progress-det (tproj i Htype) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (canonical-tup Htype Hv refl) λ
        { (ts , refl , Hvs) → _ , estep (eproj i Hvs) }
      ; (ι₂ (t′ , Hstep)) → _ , cong-step′ 0ꟳ refl (λ _ ()) Hstep
      }
  progress-det (tif Htype Htype₁ Htype₂) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (canonical-real Htype Hv refl) λ
        { (r , Heq) → _ , estep (eif Heq) }
      ; (ι₂ (t′ , Hstep)) → _ , cong-step′ 0ꟳ refl (λ _ ()) Hstep
      }
  progress-det (tdiff _ Htype Htype₁) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (progress-det Htype₁) λ
        { (ι₁ Hv₁) → _ , estep (ediff Hv Hv₁)
        ; (ι₂ (t′ , Hstep)) →
          _ , cong-step′ 1ꟳ refl (λ {0ꟳ (+1≤ 0≤) → Hv}) Hstep
        }
      ; (ι₂ (t′ , Hstep)) → _ , cong-step′ 0ꟳ refl (λ _ ()) Hstep
      }
  progress-det (tsolve Htype Htype₁ Htype₂) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (progress-det Htype₁) λ
        { (ι₁ Hv₁) → case (progress-det Htype₂) λ
          { (ι₁ Hv₂) → _ , estep (esolve Hv Hv₁ Hv₂)
          ; (ι₂ (t′ , Hstep)) →
            _ , cong-step′ 2ꟳ refl
              (λ { 0ꟳ (+1≤ 0≤) → Hv
                 ; 1ꟳ (+1≤ (+1≤ 0≤)) → Hv₁ })
              Hstep
          }
        ; (ι₂ (t′ , Hstep)) →
          _ , cong-step′ 1ꟳ refl (λ {0ꟳ (+1≤ 0≤) → Hv}) Hstep
        }
      ; (ι₂ (t′ , Hstep)) → _ , cong-step′ 0ꟳ refl (λ _ ()) Hstep
      }
  progress-det (tdist _ Htypes) =
    case (all-⊎ (progress-det ∘ Htypes)) λ
      { (ι₁ Hvs)                      → ι₁ $ vdist Hvs
      ; (ι₂ (j , (t′ , Hstep) , Hvs)) → ι₂ $
        _ , cong-step′ j refl Hvs Hstep
      }
  progress-det (texpect Htype) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (canonical-dist Htype Hv refl) λ
        { (ι₁ (D , ts , refl)) → _ , estep eexpectdist
        ; (ι₂ (v , refl , Hv)) → _ , estep (eexpectinfer Hv)
        }
      ; (ι₂ (t′ , Hstep)) → _ , cong-step′ 0ꟳ refl (λ _ ()) Hstep
      }
  progress-det (tinfer Htype) =
    case (progress-det Htype) λ
      { (ι₁ Hv)           → ι₁ $ vinfer Hv
      ; (ι₂ (t′ , Hstep)) → ι₂ $ _ , cong-step′ 0ꟳ refl (λ _ ()) Hstep
      }
  progress-det (tweaken Htype [] _) = progress-det Htype
  progress-det (tsub Htype 0≤ _)    = progress-det Htype
  progress-det (tpromote {[]} Htype refl) = progress-det Htype


  progress-rnd
    : ∀ {t T w p s}
    → [] ⊢ t :[ rnd ] T
    → -------------------------------------------------
      Value t ⊎ ∑ tws′ ∶ _ , (t , w , p :: s) →rnd tws′

  progress-rnd (tapp Htype Htype₁) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₁ Hv) → case (progress-rnd Htype₁) λ
        { (ι₁ Hv₁) → case (canonical-⇒ Htype Hv refl) λ
          { (_ , t , Heq) → _ , estep (edet (eapp Heq Hv₁)) }
        ; (ι₂ (_ , Hstep)) →
          _ , cong-step 1ꟳ refl (λ {0ꟳ (+1≤ 0≤) → Hv}) Hstep -- 
        }
      ; (ι₂ (_ , Hstep)) → _ , cong-step 0ꟳ refl (λ _ ()) Hstep
      }
  progress-rnd (tprim {ts = ts} Hϕ Htypes) =
    ι₂ $ case (all-⊎ (progress-rnd ∘ Htypes)) λ
      { (ι₁ Hvs) →
        let Hreals : ∃[ rs ] ts ≡ map real rs
            Hreals = _ , funext λ i → π₂ $ canonical-real (Htypes i) (Hvs i) refl
        in case Hreals λ { (_ , refl) → _ , estep (edet eprim) }
      ; (ι₂ (j , (_ , Hstep) , Hvs)) → _ , cong-step j refl Hvs Hstep
      }
  progress-rnd (ttup Htypes) =
    case (all-⊎ (progress-rnd ∘ Htypes)) λ
      { (ι₁ Hvs)                      → ι₁ $ vtup Hvs
      ; (ι₂ (j , (_ , Hstep) , Hvs)) → ι₂ $
        _ , cong-step j refl Hvs Hstep
      }
  progress-rnd (tproj i Htype) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₁ Hv) → case (canonical-tup Htype Hv refl) λ
        { (ts , refl , Hvs) → _ , estep (edet (eproj i Hvs)) }
      ; (ι₂ (_ , Hstep)) → _ , cong-step 0ꟳ refl (λ _ ()) Hstep
      }
  progress-rnd (tif Htype Htype₁ Htype₂) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₁ Hv) → case (canonical-real Htype Hv refl) λ
        { (r , Heq) → _ , estep (edet (eif Heq)) }
      ; (ι₂ (_ , Hstep)) → _ , cong-step 0ꟳ refl (λ _ ()) Hstep
      }
  progress-rnd (tdiff _ Htype Htype₁) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₁ Hv) → case (progress-rnd Htype₁) λ
        { (ι₁ Hv₁) → _ , estep (edet (ediff Hv Hv₁))
        ; (ι₂ (_ , Hstep)) →
          _ , cong-step 1ꟳ refl (λ {0ꟳ (+1≤ 0≤) → Hv}) Hstep
        }
      ; (ι₂ (_ , Hstep)) → _ , cong-step 0ꟳ refl (λ _ ()) Hstep
      }
  progress-rnd (tsolve Htype Htype₁ Htype₂) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₁ Hv) → case (progress-rnd Htype₁) λ
        { (ι₁ Hv₁) → case (progress-rnd Htype₂) λ
          { (ι₁ Hv₂) → _ , estep (edet (esolve Hv Hv₁ Hv₂))
          ; (ι₂ (_ , Hstep)) →
            _ , cong-step 2ꟳ refl
              (λ { 0ꟳ (+1≤ 0≤) → Hv
                 ; 1ꟳ (+1≤ (+1≤ 0≤)) → Hv₁ })
              Hstep
          }
        ; (ι₂ (_ , Hstep)) →
          _ , cong-step 1ꟳ refl (λ {0ꟳ (+1≤ 0≤) → Hv}) Hstep
        }
      ; (ι₂ (_ , Hstep)) → _ , cong-step 0ꟳ refl (λ _ ()) Hstep
      }
  progress-rnd (tdist _ Htypes) =
    case (all-⊎ (progress-rnd ∘ Htypes)) λ
      { (ι₁ Hvs)                     → ι₁ $ vdist Hvs
      ; (ι₂ (j , (_ , Hstep) , Hvs)) → ι₂ $
        _ , cong-step j refl Hvs Hstep
      }
  progress-rnd (texpect Htype) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₁ Hv) → case (canonical-dist Htype Hv refl) λ
        { (ι₁ (D , ts , refl)) → _ , estep (edet eexpectdist)
        ; (ι₂ (v , refl , Hv)) → _ , estep (edet (eexpectinfer Hv))
        }
      ; (ι₂ (_ , Hstep)) → _ , cong-step 0ꟳ refl (λ _ ()) Hstep
      }
  progress-rnd (tassume Htype) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₁ Hv) → case (canonical-dist Htype Hv refl) λ
        { (ι₁ (D , ts , refl)) → _ , estep eassumedist
        ; (ι₂ (v , refl , Hv)) → _ , estep (eassumeinfer Hv)
        }
      ; (ι₂ (_ , Hstep)) → _ , cong-step 0ꟳ refl (λ _ ()) Hstep
      }
  progress-rnd (tweight Htype) =
    ι₂ $ case (progress-rnd Htype) λ
      { (ι₁ Hv) → case (canonical-real Htype Hv refl) λ
        { (r , refl) → _ , estep eweight }
      ; (ι₂ (_ , Hstep)) → _ , cong-step 0ꟳ refl (λ _ ()) Hstep
      }
  progress-rnd (tinfer Htype) =
    case (progress-rnd Htype) λ
      { (ι₁ Hv) → ι₁ $ vinfer Hv
      ; (ι₂ (_ , Hstep)) → ι₂ $ _ , cong-step 0ꟳ refl (λ _ ()) Hstep
      }
  progress-rnd (tweaken Htype [] _) = progress-rnd Htype
  progress-rnd (tsub Htype 0≤ _) =
    case (progress-det Htype) λ
      { (ι₁ Hv) → ι₁ Hv
      ; (ι₂ (_ , Hstep)) → ι₂ $ _ , →det⊆→rnd Hstep
      }
  progress-rnd (tsub Htype (+1≤ 0≤) _) = progress-rnd Htype
  progress-rnd (tpromote {[]} Htype refl) = progress-rnd Htype
