open import Lib.Algebra.Reals

module DPPL.Properties.Typing (R : Reals₀) where

open import DPPL.Syntax R
open import DPPL.Typing R

open import Lib.Prelude
open import Lib.Data.Vector
open import Lib.LocallyNameless.Unfinite
open import Lib.Syntax.Env
open import Lib.Syntax.Substitution

open import Data.Dec.Base
open import Data.Nat.Base using (Nat-is-set)

open SyntaxVars
open TypingVars
open FinsetSyntax

ttup-inv :
  {vs : Tm ^ n}
  {Ts : Ty ^ n}
  (_ : Γ ⊢ tup n ▸ vs :[ e ] T)
  (_ : T ≡ᵢ ttup n Ts)
  → ---------------------------
  ∀ i → Γ ⊢ vs i :[ e ] Ts i
ttup-inv (ttup Htys) Heq i = subst (_ ⊢ _ :[ _ ]_)
  (is-set→cast-pathp (Ty ^_) Nat-is-set (ap snd (ttup-inj (Id≃path.to Heq))) $ₚ i)
  (Htys i)
ttup-inv (tsub Hty H≤ (stup H<:)) reflᵢ i = tsub (ttup-inv Hty reflᵢ i) H≤ (H<: i)
ttup-inv (tpromote {T = ttup _ _} Hty H≤ H⊆) reflᵢ i =
  tpromote (ttup-inv Hty reflᵢ i) H≤ H⊆

weaken-typing : Γ ⊢ t :[ e ] T → Γ ⊆ Γ' → Γ' ⊢ t :[ e ] T
weaken-typing (tsub Hty H≤ H<:) H⊆     = tsub (weaken-typing Hty H⊆) H≤ H<:
weaken-typing (tpromote Hty H≤ H⊆') H⊆ = tpromote Hty H≤ λ _ → H⊆ _ ∘ H⊆' _
weaken-typing (tvar H∈) H⊆             = tvar (H⊆ _ H∈)
weaken-typing {Γ' = Γ'} (tlam (Иi As Hty)) H⊆ = tlam $ Иi (As ∪ env-dom Γ') λ a →
  weaken-typing (Hty a ⦃ {!!} ⦄) {!!}
weaken-typing (tapp Hty Hty₁) H⊆ =
  tapp (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆)
weaken-typing (tprim Hϕ Hty) H⊆         = tprim Hϕ (weaken-typing Hty H⊆)
weaken-typing treal H⊆                  = treal
weaken-typing (ttup Htys) H⊆            = ttup λ i → weaken-typing (Htys i) H⊆
weaken-typing (tproj i Hty) H⊆          = tproj i (weaken-typing Hty H⊆)
weaken-typing (tif Hty Hty₁ Hty₂ H≤) H⊆ =
  tif (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) (weaken-typing Hty₂ H⊆) H≤
weaken-typing tuniform H⊆ = tuniform
weaken-typing (tsample Hty) H⊆ = tsample (weaken-typing Hty H⊆)
weaken-typing (tweight Hty) H⊆ = tweight (weaken-typing Hty H⊆)
weaken-typing (tinfer Hty) H⊆  = tinfer (weaken-typing Hty H⊆)
weaken-typing (tdiff Hty Hty₁ Hc) H⊆ =
  tdiff (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) Hc
weaken-typing (tsolve Hty Hty₁ Hty₂ Hc) H⊆ =
  tsolve (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) (weaken-typing Hty₂ H⊆) Hc

substitution-pres-typing :
  {x : 𝔸}
  {t u : Tm}
  {T₁ T₂ : Ty}
  (_ : [ x ∶ T₂ ] & Γ' ⊢ t :[ e ] T₁)
  (_ : ε ⊢ u :[ det ] T₂)
  → ---------------------------------
  ε & Γ' ⊢ (x => u) t :[ e ] T₁
substitution-pres-typing {x = x} {u = u} {T₂ = T₂} Hty Hu = go ⦃ reflᵢ ⦄ Hty where
  go :
    {Γ' Γ₀ : TyEnv}
    {T₁ : Ty}
    ⦃ _ : Γ₀ ≡ᵢ ([ x ∶ T₂ ] & Γ') ⦄
    (_ : Γ₀ ⊢ t :[ e ] T₁)
    → ----------------------------
    ε & Γ' ⊢ (x => u) t :[ e ] T₁
  go ⦃ reflᵢ ⦄ (tvar {a = a} H∈) with x ≡? a
  ... | yes x≡a = {!!}
  ... | no  x≠a = tvar {!!}
  go (tlam (Иi As Hty)) = tlam $ Иi ([ x ] ∪ As) λ a → {!!}
  go (tapp Hty Hty₁)           = tapp (go Hty) (go Hty₁)
  go (tprim Hϕ Hty)            = tprim Hϕ (go Hty)
  go treal                     = treal
  go (ttup Htys)               = ttup (go ∘ Htys)
  go (tproj i Hty)             = tproj i (go Hty)
  go (tif Hty Hty₁ Hty₂ H≤)    = tif (go Hty) (go Hty₁) (go Hty₂) H≤
  go tuniform                  = tuniform
  go (tsample Hty)             = tsample (go Hty)
  go (tweight Hty)             = tweight (go Hty)
  go (tinfer Hty)              = tinfer (go Hty)
  go (tdiff Hty Htype₁ Hc)     = tdiff (go Hty) (go Htype₁) Hc
  go (tsolve Hty Hty₁ Hty₂ Hc) = tsolve (go Hty) (go Hty₁) (go Hty₂) Hc
  go (tsub Hty H≤ H<:)         = tsub (go Hty) H≤ H<:
  go (tpromote Hty H≤ H⊆)      =
    tpromote (go ⦃ {!!} ⦄ Hty) {!!} {!!}
