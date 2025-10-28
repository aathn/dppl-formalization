open import Lib.Algebra.Reals

module DPPL.Properties.Typing (R : Reals₀) where

open import DPPL.Syntax R
open import DPPL.Typing R

open import Lib.Prelude
open import Lib.Data.Dec
open import Lib.Data.Vector
open import Lib.Data.Finset
open import Lib.LocallyNameless.Unfinite
open import Lib.Syntax.Env
open import Lib.Syntax.Substitution

open import Data.Dec.Base
open import Data.Nat.Base using (Nat-is-set)
open import Data.Finset.Base

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
weaken-typing (tpromote Hty H≤ H⊆') H⊆ = tpromote Hty H≤ (env-sub-trans H⊆' H⊆)
weaken-typing (tvar H∈) H⊆             = tvar (env-sub-trans H∈ H⊆)
weaken-typing {Γ' = Γ'} (tlam (Иi As Hty)) H⊆ = tlam $ Иi (As ∪ env-dom Γ') λ a →
  weaken-typing (Hty a ⦃ ∉∪₁ auto ⦄) (env-sub-cons reflᵢ (∉∪₂ As auto) H⊆)
weaken-typing (tapp Hty Hty₁) H⊆ =
  tapp (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆)
weaken-typing (tprim Hϕ Hty) H⊆         = tprim Hϕ (weaken-typing Hty H⊆)
weaken-typing treal H⊆                  = treal
weaken-typing (ttup Htys) H⊆            = ttup λ i → weaken-typing (Htys i) H⊆
weaken-typing (tproj i Hty) H⊆          = tproj i (weaken-typing Hty H⊆)
weaken-typing (tif Hty Hty₁ Hty₂ H≤) H⊆ =
  tif (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) (weaken-typing Hty₂ H⊆) H≤
weaken-typing tuniform H⊆            = tuniform
weaken-typing (tsample Hty) H⊆       = tsample (weaken-typing Hty H⊆)
weaken-typing (tweight Hty) H⊆       = tweight (weaken-typing Hty H⊆)
weaken-typing (tinfer Hty) H⊆        = tinfer (weaken-typing Hty H⊆)
weaken-typing (tdiff Hty Hty₁ Hc) H⊆ =
  tdiff (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) Hc
weaken-typing (tsolve Hty Hty₁ Hty₂ Hc) H⊆ =
  tsolve (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) (weaken-typing Hty₂ H⊆) Hc

subst-pres-typing :
  {x : 𝔸}
  {t u : Tm}
  {T₁ T₂ : Ty}
  (_ : [ x ∶ T₂ ] & Γ' ⊢ t :[ e ] T₁)
  (_ : ε ⊢ u :[ det ] T₂)
  → ---------------------------------
  Γ' ⊢ (x => u) t :[ e ] T₁
subst-pres-typing {x = x} (tvar {a = a} H∈) Hu with x ≡? a
... | yes x≡a with reflᵢ ← env-mem-inv (env-mem-++r (subst (_∈ᶠˢ _) x≡a hereₛ) H∈) =
  weaken-typing Hu env-sub-nil
... | no x≠a = tvar (env-mem-++l (∉∷ (false→is-no (x≠a ∘ sym)) tt) H∈)
subst-pres-typing {x = x} (tlam (Иi As Hty)) Hu = tlam $ Иi ([ x ] ∪ As) λ a →
  {!!}
subst-pres-typing (tapp Hty Hty₁) Hu =
  tapp (subst-pres-typing Hty Hu) (subst-pres-typing Hty₁ Hu)
subst-pres-typing (tprim Hϕ Hty) Hu = tprim Hϕ (subst-pres-typing Hty Hu)
subst-pres-typing treal Hu          = treal
subst-pres-typing (ttup Htys) Hu    = ttup λ i → subst-pres-typing (Htys i) Hu
subst-pres-typing (tproj i Hty) Hu  = tproj i (subst-pres-typing Hty Hu)
subst-pres-typing (tif Hty Hty₁ Hty₂ H≤) Hu = tif
  (subst-pres-typing Hty Hu) (subst-pres-typing Hty₁ Hu) (subst-pres-typing Hty₂ Hu)
  H≤
subst-pres-typing tuniform Hu            = tuniform
subst-pres-typing (tsample Hty) Hu       = tsample (subst-pres-typing Hty Hu)
subst-pres-typing (tweight Hty) Hu       = tweight (subst-pres-typing Hty Hu)
subst-pres-typing (tinfer Hty) Hu        = tinfer (subst-pres-typing Hty Hu)
subst-pres-typing (tdiff Hty Hty₁ Hc) Hu =
  tdiff (subst-pres-typing Hty Hu) (subst-pres-typing Hty₁ Hu) Hc
subst-pres-typing (tsolve Hty Hty₁ Hty₂ Hc) Hu = tsolve
  (subst-pres-typing Hty Hu) (subst-pres-typing Hty₁ Hu) (subst-pres-typing Hty₂ Hu)
  Hc
subst-pres-typing (tsub Hty H≤ H<:) Hu    = tsub (subst-pres-typing Hty Hu) H≤ H<:
subst-pres-typing (tpromote Hty H≤ H⊆) Hu = {!!}
