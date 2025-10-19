open import Lib.Algebra.Reals

module DPPL.Properties.Typing (R : Reals₀) where

open import 1Lab.Prelude

open import DPPL.Syntax R
open import DPPL.Typing R

open import Lib.Data.Vector
open import Lib.LocallyNameless.Unfinite
open import Lib.Syntax.Env
open import Lib.Syntax.Substitution

open import Data.Nat.Base using (Nat-is-set)

open SyntaxVars
open TypingVars

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


substitution-pres-typing :
  {x : 𝔸}
  {t u : Tm}
  {T₁ T₂ : Ty}
  (_ : [ x ∶ T₂ ] & Γ' ⊢ t :[ e ] T₁)
  (_ : ε ⊢ u :[ det ] T₂)
  → ---------------------------------
  ε & Γ' ⊢ (x => u) t :[ e ] T₁
substitution-pres-typing {Γ' = Γ'} {x = x} {u = u} {T₂ = T₂} Htype Hu = {!!}
