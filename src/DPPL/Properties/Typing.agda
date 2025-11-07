open import Lib.Algebra.Reals

module DPPL.Properties.Typing (R : Reals₀) where

open import DPPL.Syntax R
open import DPPL.Typing R

open import Lib.Prelude
open import Lib.Data.Dec
open import Lib.Data.Vector
open import Lib.Data.Finset
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.BindingSignature
open import Lib.LocallyNameless.oc-Sets
open import Lib.LocallyNameless.AbstractionConcretion

open import Lib.Syntax.Env
open import Lib.Syntax.Substitution

open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Nat.Base using (Nat-is-set)
open import Data.Finset.Base

open SyntaxVars
open TypingVars
open FinsetSyntax
open LocalClosed
open Body

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

∉-dom-fv :
  {x : 𝔸}
  (_ : Γ ⊢ t :[ e ] T)
  (_ : x ∉ env-dom Γ)
  → ------------------
  x ∉ fv t
∉-dom-fv = {!!}

well-typed→lc : Γ ⊢ t :[ e ] T → lc-at 0 t
well-typed→lc (tsub Hty _ _)             = well-typed→lc Hty
well-typed→lc (tpromote Hty _ _)         = well-typed→lc Hty
well-typed→lc (tvar _)                   = lc-at-fvar
well-typed→lc (tlam {t = t} (Иi As Hty)) =
  let Hbody : body (t ₀)
      Hbody = Иi As λ x → lc-at→≻ _ _ $ well-typed→lc (Hty x)
  in lc-at-op $ Fin-cases (≻→lc-at _ _ $ body→1≻ _ Hbody) λ ()
well-typed→lc (tapp Hty Hty₁) = lc-at-op
  $ Fin-cases (well-typed→lc Hty)
  $ Fin-cases (well-typed→lc Hty₁) λ ()
well-typed→lc (tprim Hϕ Hty) = lc-at-op $ Fin-cases (well-typed→lc Hty) λ ()
well-typed→lc treal          = lc-at-op λ ()
well-typed→lc (ttup Htys)    = lc-at-op λ k → well-typed→lc (Htys k)
well-typed→lc (tproj i Hty)  = lc-at-op $ Fin-cases (well-typed→lc Hty) λ ()
well-typed→lc (tif Hty Hty₁ Hty₂ H≤) = lc-at-op
  $ Fin-cases (well-typed→lc Hty)
  $ Fin-cases (well-typed→lc Hty₁)
  $ Fin-cases (well-typed→lc Hty₂) λ ()
well-typed→lc tuniform      = lc-at-op λ ()
well-typed→lc (tsample Hty) = lc-at-op $ Fin-cases (well-typed→lc Hty) λ ()
well-typed→lc (tweight Hty) = lc-at-op $ Fin-cases (well-typed→lc Hty) λ ()
well-typed→lc (tinfer Hty)  = lc-at-op $ Fin-cases (well-typed→lc Hty) λ ()
well-typed→lc (tdiff Hty Hty₁ Hc) = lc-at-op
  $ Fin-cases (well-typed→lc Hty)
  $ Fin-cases (well-typed→lc Hty₁) λ ()
well-typed→lc (tsolve Hty Hty₁ Hty₂ Hc) = lc-at-op
  $ Fin-cases (well-typed→lc Hty)
  $ Fin-cases (well-typed→lc Hty₁)
  $ Fin-cases (well-typed→lc Hty₂) λ ()

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
  (_ : Γ' ≡ᵢ [ x ∶ T₂ ] & Γ)
  (_ : ε ⊢ u :[ det ] T₂)
  (_ : Γ' ⊢ t :[ e ] T₁)
  → --------------------------
  Γ ⊢ (x => u) t :[ e ] T₁
subst-pres-typing {x = x} reflᵢ Hu (tvar {a = a} H∈) with x ≡? a
... | yes x≡a with reflᵢ ← env-mem-inv (env-mem-++r (subst (_∈ᶠˢ _) x≡a hereₛ) H∈) =
  weaken-typing Hu env-sub-nil
... | no x≠a = tvar (env-mem-++l (∉∷ (false→is-no (x≠a ∘ sym)) tt) H∈)
subst-pres-typing {Γ = Γ} {x = x} {u = u} {T₂ = T₂} reflᵢ Hu
  (tlam {T = T} {e} {T'} {t = t} (Иi As Hty)) = tlam $ Иi ([ x ] ∪ As) λ a ⦃ H∉ ⦄ →
  let Heq : (x => u)((0 ~> a) (t ₀)) ≡ (0 ~> a)((x => u) (t ₀))
      Heq = subst-open-comm (t ₀) (sym≠ a x (∉∷₁ H∉)) (lc-at→≻ _ _ $ well-typed→lc Hu)
  in subst (λ x → _ ⊢ x :[ _ ] _) Heq
     $ subst-pres-typing (Id≃path.from (env-cons-& _ _)) Hu (Hty a ⦃ ∉∷₂ H∉ ⦄)
subst-pres-typing HΓ Hu (tapp Hty Hty₁) =
  tapp (subst-pres-typing HΓ Hu Hty) (subst-pres-typing HΓ Hu Hty₁)
subst-pres-typing HΓ Hu (tprim Hϕ Hty) = tprim Hϕ (subst-pres-typing HΓ Hu Hty)
subst-pres-typing HΓ Hu treal          = treal
subst-pres-typing HΓ Hu (ttup Htys)    = ttup λ i → subst-pres-typing HΓ Hu (Htys i)
subst-pres-typing HΓ Hu (tproj i Hty)  = tproj i (subst-pres-typing HΓ Hu Hty)
subst-pres-typing HΓ Hu (tif Hty Hty₁ Hty₂ H≤) = tif
  (subst-pres-typing HΓ Hu Hty)
  (subst-pres-typing HΓ Hu Hty₁)
  (subst-pres-typing HΓ Hu Hty₂)
  H≤
subst-pres-typing HΓ Hu tuniform            = tuniform
subst-pres-typing HΓ Hu (tsample Hty)       = tsample (subst-pres-typing HΓ Hu Hty)
subst-pres-typing HΓ Hu (tweight Hty)       = tweight (subst-pres-typing HΓ Hu Hty)
subst-pres-typing HΓ Hu (tinfer Hty)        = tinfer (subst-pres-typing HΓ Hu Hty)
subst-pres-typing HΓ Hu (tdiff Hty Hty₁ Hc) =
  tdiff (subst-pres-typing HΓ Hu Hty) (subst-pres-typing HΓ Hu Hty₁) Hc
subst-pres-typing HΓ Hu (tsolve Hty Hty₁ Hty₂ Hc) = tsolve
  (subst-pres-typing HΓ Hu Hty)
  (subst-pres-typing HΓ Hu Hty₁)
  (subst-pres-typing HΓ Hu Hty₂)
  Hc
subst-pres-typing HΓ Hu (tsub Hty H≤ H<:) = tsub (subst-pres-typing HΓ Hu Hty) H≤ H<:
subst-pres-typing {Γ = Γ} {x = x} reflᵢ Hu
  (tpromote {Γ = Γ'} Hty H≤ H⊆) with holds? (x ∈ env-dom Γ')
... | yes H∈
  with Γ'' , H⊆' , Heq , H∉ ← env-sub-split H∈ H⊆
  rewrite Id≃path.from Heq = tpromote
    (subst-pres-typing reflᵢ Hu Hty)
    (λ H∈ → H≤ (env-sub-trans H∈ (env-sub-&r H∉ env-sub-refl)))
    H⊆'
... | no H∉ = tpromote
  (subst (_ ⊢_:[ _ ] _) (sym $ subst-fresh _ _ (∉-dom-fv Hty (false→is-no H∉))) Hty)
  H≤
  (env-sub-strengthen (false→is-no H∉) H⊆)
