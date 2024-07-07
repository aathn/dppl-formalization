module Properties.Typing (ℝ : Set) where

-- Lemmas purely about typing

open import Lib.Prelude

open import Function using (flip)
open import Data.List using (_++_)

open import Syntax ℝ
open import Typing ℝ

infixl 5 _&_
_&_ : TyEnv → TyEnv → TyEnv
_&_ = flip _++_

substitution-pres-typing
  : ∀ {Γ′ Γ₀ Γ t x T₁ e T₂ u}
  → Γ₀ ⊢ t :[ e ] T₂
  → Γ  ⊢ u :[ e ] T₁
  → Γ₀ ≡ Γ , x ∶ T₁ & Γ′ 
  → ------------------------
    Γ & Γ′ ⊢ (x => u) t :[ e ] T₂
substitution-pres-typing tvar Hu Heq = {!!}
substitution-pres-typing (tabs x) Hu Heq = {!!}
substitution-pres-typing (tapp Htype Htype₁) Hu Heq = {!!}
substitution-pres-typing (tprim x x₁) Hu Heq = {!!}
substitution-pres-typing treal Hu Heq = {!!} -- tweaken treal ? ?
substitution-pres-typing (ttup x) Hu Heq = {!!}
substitution-pres-typing (tproj i Htype) Hu Heq = {!!}
substitution-pres-typing (tif Htype Htype₁ Htype₂) Hu Heq = {!!}
substitution-pres-typing (tdiff x Htype Htype₁) Hu Heq = {!!}
substitution-pres-typing (tsolve Htype Htype₁ Htype₂) Hu Heq = {!!}
substitution-pres-typing (tdist x x₁) Hu Heq = {!!}
substitution-pres-typing (tassume Htype) Hu Heq = {!!}
substitution-pres-typing (tweight Htype) Hu Heq = {!!}
substitution-pres-typing (texpect Htype) Hu Heq = {!!}
substitution-pres-typing (tinfer Htype) Hu Heq = {!!}
substitution-pres-typing (tweaken Htype x x₁) Hu Heq = {!!}
substitution-pres-typing (tsub Htype x x₁) Hu Heq = {!!}
substitution-pres-typing (tpromote Htype x) Hu Heq = {!!}
