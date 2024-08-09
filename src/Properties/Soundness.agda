module Properties.Soundness (ℝ 𝕀 : Set) where

open import Lib.Prelude

import Data.List as L
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star ; ε ; _◅_)

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ 𝕀
open import Properties.Preservation ℝ 𝕀
open import Properties.Progress ℝ 𝕀
open import Properties.SmallStep ℝ 𝕀

module Soundness (Ass : EvalAssumptions) (PAss : PresAssumptions Ass) where
  open Eval Ass
  open Step Ass
  open Progress Ass
  open Preservation Ass PAss

  ∥_∥ : {A : Set} {T : Rel A ℓ₀} {a b : A} → Star T a b → ℕ
  ∥ ε ∥ = 0
  ∥ _ ◅ Hs ∥ = ∥ Hs ∥ +1

  type-system-sound-det
    : ∀ {n t T}
    → [] ⊢ t :[ det ] T
    → ------------------------------------
      ∑ t′ ∶ Term , ∑ Hstep ∶ t →det* t′ ,
      [] ⊢ t′ :[ det ] T × (Value t′ ⊎ ∥ Hstep ∥ ≡ n)

  type-system-sound-det {n = 0} {t} Htype = t , ε , Htype , ι₂ refl
  type-system-sound-det {n = _+1 n} {t} Htype with progress-det Htype
  ... | ι₁ Hv = t , ε , Htype , ι₁ Hv
  ... | ι₂ (t′ , Hstep)
    with type-system-sound-det {n} {t′} (preservation-det Htype Hstep)
  ... | t″ , Hstep′ , Htype′ , ι₁ Hv = t″ , Hstep ◅ Hstep′ , Htype′ , ι₁ Hv
  ... | t″ , Hstep′ , Htype′ , ι₂ refl = t″ , Hstep ◅ Hstep′ , Htype′ , ι₂ refl

  type-system-sound-rnd
    : ∀ {n t w s T}
    → [] ⊢ t :[ rnd ] T
    → L.length s ≥ n
    → --------------------------------------
      ∑ (t′ , w′ , s′) ∶ Term × ℝ × List 𝕀 ,
      ∑ Hstep ∶ (t , w , s) →rnd* (t′ , w′ , s′) ,
      [] ⊢ t′ :[ rnd ] T × (Value t′ ⊎ ∥ Hstep ∥ ≡ n)

  type-system-sound-rnd {n = ₀} {t} {w} {s} Htype H≥ =
    (t , w , s) , ε , Htype , ι₂ refl
  type-system-sound-rnd {n = _+1 n} {t} {w} {p :: s} Htype (+1≤ H≥)
    with progress-rnd {w = w} {p} {s} Htype
  ... | ι₁ Hv = (t , w , p :: s) , ε , Htype , ι₁ Hv
  ... | ι₂ ((t′ , w′ , s′) , Hstep)
    with type-system-sound-rnd {n} {t′} {w′} {s′}
           (preservation-rnd Htype Hstep) (≤trans H≥ (trace-length Hstep refl))
  ... | tws″ , Hstep′ , Htype′ , ι₁ Hv = tws″ , Hstep ◅ Hstep′ , Htype′ , ι₁ Hv
  ... | tws″ , Hstep′ , Htype′ , ι₂ refl = tws″ , Hstep ◅ Hstep′ , Htype′ , ι₂ refl
