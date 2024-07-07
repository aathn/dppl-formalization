module Properties (ℝ : Set) where

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ

open import Lib.Prelude
open import Lib.FunExt
open import Lib.BindingSignature

open import Function using (_$_ ; const)
open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.List.Relation.Binary.Sublist.Propositional using ([])
open import Data.Product using (∃-syntax)
open import Data.Vec.Functional using (map)

module _ (Ass : EvalAssumptions) where
  open Eval Ass

  _→det_ : Term → Term → Set
  _→det_ = CongCls _→ᵈ_

  -- Utility lemmas

  all-⊎
    : ∀ {n} {A B : Fin n → Set}
    → (∀ i → A i ⊎ B i)
    → (∀ i → A i) ⊎ ∃[ j ] B j × ∀ (i : Fin n) → i <ꟳ j → A i
  all-⊎ {zero} f = ι₁ λ()
  all-⊎ {n +1} f =
    case (f zero) λ
      { (ι₁ Ha) →
        case (all-⊎ (f ∘ succ)) λ
          { (ι₁ Has) → ι₁ $ λ { zero → Ha ; (succ n) → Has n }
          ; (ι₂ (j , Hb , Has)) → ι₂ $
            _ , Hb , λ { zero _ → Ha ; (succ n) H≤ → Has n (≤-1 H≤) }
          }
      ; (ι₂ Hb) → ι₂ $ _ , Hb , λ _ ()
      }

  -- Canonical forms

  canonical-⇒
    : ∀ {Γ t e e′ T T₁ T₂}
    → Γ ⊢ t :[ e ] T
    → Value t
    → T ≡ T₁ ⇒[ e′ ] T₂
    → -----------------------------
      ∃[ T′ ] ∃[ t′ ] t ≡ abs T′ t′
  canonical-⇒ (tabs _) _ refl = _ , _ , refl
  canonical-⇒ (tweaken Htype _ _) Hval Heq =
    canonical-⇒ Htype Hval Heq
  canonical-⇒ (tsub Htype _ (sarr _ _ _)) Hval refl =
    canonical-⇒ Htype Hval refl
  canonical-⇒ (tpromote {T = _ ⇒[ _ ] _} Htype refl) Hval Heq =
    canonical-⇒ Htype Hval Heq

  canonical-real
    : ∀ {Γ t e T c}
    → Γ ⊢ t :[ e ] T
    → Value t
    → T ≡ treal c
    → -----------------
      ∃[ r ] t ≡ real r
  canonical-real treal _ _ = _ , refl
  canonical-real (tweaken Htype _ _) Hval Heq =
    canonical-real Htype Hval Heq
  canonical-real (tsub Htype _ (sreal _)) Hval refl =
    canonical-real Htype Hval refl
  canonical-real (tpromote {T = treal _} Htype refl) Hval refl =
    canonical-real Htype Hval refl

  canonical-tup
    : ∀ {Γ t e T n Ts}
    → Γ ⊢ t :[ e ] T
    → Value t
    → T ≡ ttup {n} Ts
    → -------------------------------------------
      ∃[ ts ] t ≡ tup {n} ts × ∀ i → Value (ts i)
  canonical-tup (ttup _) (vtup Hvs) refl = _ , refl , Hvs
  canonical-tup (tweaken Htype _ _) Hval Heq =
    canonical-tup Htype Hval Heq
  canonical-tup (tsub Htype _ (stup _)) Hval refl =
    canonical-tup Htype Hval refl
  canonical-tup (tpromote {T = ttup _} Htype refl) Hval refl =
    canonical-tup Htype Hval refl

  canonical-dist
    : ∀ {Γ t e T T′}
    → Γ ⊢ t :[ e ] T
    → Value t
    → T ≡ tdist T′
    → -----------------------------------------
      (∃[ D ] ∃[ rs ] t ≡ dist D (map real rs))
    ⊎ (∃[ v ] t ≡ infer v × Value v)
  canonical-dist (tdist {ts = ts} _ Htypes) (vdist Hvs) _ =
    let Hreals : ∃[ rs ] ts ≡ map real rs
        Hreals = _ , funext λ i → π₂ $ canonical-real (Htypes i) (Hvs i) refl
    in
    case Hreals λ { (_ , refl) → ι₁ $ _ , _ , refl }
  canonical-dist (tinfer _) Hval refl = ι₂ $ infer-inv Hval refl
    where
    infer-inv : ∀ {t t′} → Value t′ → t′ ≡ infer t → ∃[ v ] infer t ≡ infer v × Value v
    infer-inv (vinfer Hv) Heq = _ , symm Heq , Hv
  canonical-dist (tweaken Htype _ _) Hval Heq =
    canonical-dist Htype Hval Heq
  canonical-dist (tsub Htype _ (sdist _)) Hval refl =
    canonical-dist Htype Hval refl
  canonical-dist (tpromote {T = tdist _} Htype refl) Hval Heq =
    canonical-dist Htype Hval Heq

  -- Progress

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
          { (_ , t , refl) → _ , estep (eapp Hv₁) }
        ; (ι₂ (t′ , Hstep)) →
          cong-step (succ zero) refl (λ {zero (+1≤ 0≤) → Hv}) Hstep
        }
      ; (ι₂ (t′ , Hstep)) → cong-step zero refl (λ _ ()) Hstep
      }
  progress-det (tprim {ts = ts} Hϕ Htypes) =
    ι₂ $ case (all-⊎ (progress-det ∘ Htypes)) λ
      { (ι₁ Hvs) →
        let Hreals : ∃[ rs ] ts ≡ map real rs
            Hreals = _ , funext λ i → π₂ $ canonical-real (Htypes i) (Hvs i) refl
        in case Hreals λ { (_ , refl) → _ , estep eprim }
      ; (ι₂ (j , (t′ , Hstep) , Hvs)) → cong-step j refl Hvs Hstep
      }
  progress-det (ttup Htypes) =
    case (all-⊎ (progress-det ∘ Htypes)) λ
      { (ι₁ Hvs)                      → ι₁ $ vtup Hvs
      ; (ι₂ (j , (t′ , Hstep) , Hvs)) → ι₂ $
        cong-step j refl Hvs Hstep
      }
  progress-det (tproj i Htype) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (canonical-tup Htype Hv refl) λ
        { (ts , refl , Hvs) → _ , estep (eproj i Hvs) }
      ; (ι₂ (t′ , Hstep)) → cong-step zero refl (λ _ ()) Hstep
      }
  progress-det (tif Htype Htype₁ Htype₂) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (canonical-real Htype Hv refl) λ
        { (r , refl) → _ , estep eif }
      ; (ι₂ (t′ , Hstep)) → cong-step zero refl (λ _ ()) Hstep
      }
  progress-det (tdiff _ Htype Htype₁) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (progress-det Htype₁) λ
        { (ι₁ Hv₁) → _ , estep (ediff Hv Hv₁)
        ; (ι₂ (t′ , Hstep)) →
          cong-step (succ zero) refl (λ {zero (+1≤ 0≤) → Hv}) Hstep
        }
      ; (ι₂ (t′ , Hstep)) → cong-step zero refl (λ _ ()) Hstep
      }
  progress-det (tsolve Htype Htype₁ Htype₂) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (progress-det Htype₁) λ
        { (ι₁ Hv₁) → case (progress-det Htype₂) λ
          { (ι₁ Hv₂) → _ , estep (esolve Hv Hv₁ Hv₂)
          ; (ι₂ (t′ , Hstep)) →
            cong-step (succ (succ zero)) refl
              (λ { zero (+1≤ 0≤) → Hv
                 ; (succ zero) (+1≤ (+1≤ 0≤)) → Hv₁ })
              Hstep
          }
        ; (ι₂ (t′ , Hstep)) →
          cong-step (succ zero) refl (λ {zero (+1≤ 0≤) → Hv}) Hstep
        }
      ; (ι₂ (t′ , Hstep)) → cong-step zero refl (λ _ ()) Hstep
      }
  progress-det (tdist _ Htypes) =
    case (all-⊎ (progress-det ∘ Htypes)) λ
      { (ι₁ Hvs)                      → ι₁ $ vdist Hvs
      ; (ι₂ (j , (t′ , Hstep) , Hvs)) → ι₂ $
        cong-step j refl Hvs Hstep
      }
  progress-det (texpect Htype) =
    ι₂ $ case (progress-det Htype) λ
      { (ι₁ Hv) → case (canonical-dist Htype Hv refl) λ
        { (ι₁ (D , ts , refl)) → _ , estep eexpectdist
        ; (ι₂ (v , refl , Hv)) → _ , estep (eexpectinfer Hv)
        }
      ; (ι₂ (t′ , Hstep)) → cong-step zero refl (λ _ ()) Hstep
      }
  progress-det (tinfer Htype) =
    case (progress-det Htype) λ
      { (ι₁ Hv)           → ι₁ $ vinfer Hv
      ; (ι₂ (t′ , Hstep)) → ι₂ $ cong-step zero refl (λ _ ()) Hstep
      }
  progress-det (tweaken Htype [] _) = progress-det Htype
  progress-det (tsub Htype 0≤ _)    = progress-det Htype
  progress-det (tpromote {[]} Htype refl) = progress-det Htype
