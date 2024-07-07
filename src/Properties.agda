module Properties (ℝ : Set) where

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ

open import Lib.Prelude
-- open import Lib.FunExt

open import Function using (_$_ ; const)
open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.List.Relation.Binary.Sublist.Propositional using ([])
open import Data.Product using (∃-syntax)

module _ (Ass : EvalAssumptions) where
  open Eval Ass

  _→det_ : Term → Term → Set
  _→det_ = CongCls _→ᵈ_

  progress-det
    : ∀ {t T}
    → [] ⊢ t :[ det ] T
    → ------------------------------
      Value t ⊎ ∑ t′ ∶ _ , t →det t′
  progress-det (tabs _) = ι₁ vabs
  progress-det treal    = ι₁ vreal
  progress-det (tapp Htype Htype₁) = {!!}
  progress-det (tprim ϕ ts) = {!!}
  progress-det (ttup {n} {Ts = Ts} {ts} Htypes) = {!!}
    -- case (progress-det (ts zero)) λ
    --   { (ι₁ Hv)           → {!!} -- ₁ (vinfer Hv)
    --   ; (ι₂ (t′ , Hstep)) → {!!}
    --   }
    where
      foo : (∀ i → [] ⊢ ts i :[ det ] Ts i)
          → (∀ i → Value (ts i)) ⊎
              ∃[ j ] ∃[ t′ ]
                ts j →det t′ × ∀ i → i <ꟳ j → Value (ts i)
      foo = {!!}
  progress-det (tproj Htype) = ι₂ $
    case (progress-det Htype) λ
      { (ι₁ Hv)           → {!!} -- ₁ (vinfer Hv)
      ; (ι₂ (t′ , Hstep)) → (_ , econg (single-ctx refl refl) Hstep)
      }
  progress-det (tif Htype Htype₁ Htype₂)    = {!!}
  progress-det (tdiff _ Htype Htype₁)       = {!!}
  progress-det (tsolve Htype Htype₁ Htype₂) = {!!}
  progress-det (tdist D ts)    = {!!}
  progress-det (texpect Htype) = ι₂ $
    case (progress-det Htype) λ
      { (ι₁ Hv)           → {!!} -- ₁ (vinfer Hv)
      ; (ι₂ (t′ , Hstep)) → (_ , econg (single-ctx refl refl) Hstep)
      }
  progress-det (tinfer Htype) =
    case (progress-det Htype) λ
      { (ι₁ Hv)           → ι₁ (vinfer Hv)
      ; (ι₂ (t′ , Hstep)) → ι₂ (_ , econg (single-ctx refl refl) Hstep)
      }
  progress-det (tweaken Htype [] _) = progress-det Htype
  progress-det (tsub Htype 0≤ _)    = progress-det Htype
  progress-det (tpromote {[]} Htype refl) = progress-det Htype
