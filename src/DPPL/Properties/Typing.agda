open import Data.Finset.Base
open import Data.Dec.Base
open import Data.Nat.Base using (Nat-is-set)

open import DPPL.Regularity

open import Lib.LocallyNameless.AbstractionConcretion
open import Lib.LocallyNameless.BindingSignature
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets
open import Lib.Syntax.Substitution
open import Lib.Algebra.Reals
open import Lib.Data.Finset
open import Lib.Data.Vector
open import Lib.Syntax.Env
open import Lib.Data.Dec
open import Lib.Prelude

open import Order.Base

import DPPL.Syntax as Syntax
import DPPL.Typing as Typing

module DPPL.Properties.Typing (R : Reals₀) where

open Syntax R renaming (_▸_ to _▹_)
open SyntaxVars
open Typing R
open TypingVars

open FinsetSyntax
open LocalClosed
open Body

tsub-refl : T <: T
tsub-refl {treal c}    = sreal (Reg↓.≤-refl {c})
tsub-refl {_ ⇒[ X ] _} = sarr tsub-refl (Reg⊆.≤-refl {X}) tsub-refl
tsub-refl {ttup _ ts}  = stup (λ i → tsub-refl)

tsub-trans : {T₁ T₂ T₃ : Ty} → T₁ <: T₂ → T₂ <: T₃ → T₁ <: T₃
tsub-trans (sreal {c} H⊆) (sreal {c'} {c''} H⊆') =
  sreal (Reg↓.≤-trans {c} {c'} {c''} H⊆ H⊆')
tsub-trans (stup H<:) (stup H<:₁) = stup λ i → tsub-trans (H<: i) (H<:₁ i)
tsub-trans (sarr {X} H<: H⊆ H<:₁) (sarr {X'} {X''} H<:' H⊆' H<:₁') = sarr
  (tsub-trans H<:' H<:) (Reg⊆.≤-trans {X} {X'} {X''} H⊆ H⊆') (tsub-trans H<:₁ H<:₁')

∉-dom-fv :
  {x : 𝔸}
  (_ : Γ ⊢ t ∶ T)
  (_ : x ∉ dom Γ)
  → ------------------
  x ∉ fv t
∉-dom-fv (tsub Hty _) H∉          = ∉-dom-fv Hty H∉
∉-dom-fv (tpromote Hty _ _ H⊆) H∉ =
  ∉-dom-fv Hty (false→is-no λ H∈ → is-no→false H∉ (env-sub→dom-sub H⊆ _ H∈))
∉-dom-fv (tvar H∈) H∉ = ∉∷
  (false→is-no λ p → is-no→false H∉ (env-sub→dom-sub H∈ _ (hereₛ' (Id≃path.from p))))
  tt
∉-dom-fv {Γ = Γ} {x = x} (tlam {t = t} (Иi As Hty)) H∉ =
  let y , H∉y = fresh{𝔸} ([ x ] ∪ As)
      H∉' = ∉-dom-fv {x = x} (Hty y ⦃ ∉∷₂ H∉y ⦄)
        $ subst (_ ∉_) (sym $ dom-cons Γ) (∉∷ (sym≠ _ _ (∉∷₁ H∉y)) H∉)
  in ∉∪ (open-notin (t ₀) H∉') tt
∉-dom-fv (tapp {ts = ts} Hty Hty₁) H∉ = ∉⋃' (fv ∘ ts)
  $ Fin-cases (∉-dom-fv Hty H∉)
  $ Fin-cases (∉-dom-fv Hty₁ H∉) λ ()
∉-dom-fv (tprim {t = t} Hϕ Hty) H∉ = ∉⋃' (fv ∘ t) $ Fin-cases (∉-dom-fv Hty H∉) λ ()
∉-dom-fv treal H∉                  = tt
∉-dom-fv (ttup {ts = ts} Htys) H∉  = ∉⋃' (fv ∘ ts) λ i → ∉-dom-fv (Htys i) H∉
∉-dom-fv (tproj {t = t} i Hty) H∉  = ∉⋃' (fv ∘ t) $ Fin-cases (∉-dom-fv Hty H∉) λ ()
∉-dom-fv (tif {ts = ts} Hty Hty₁ Hty₂ H≤) H∉ = ∉⋃' (fv ∘ ts)
  $ Fin-cases (∉-dom-fv Hty H∉)
  $ Fin-cases (∉-dom-fv Hty₁ H∉)
  $ Fin-cases (∉-dom-fv Hty₂ H∉) λ ()
∉-dom-fv (tdiff {ts = ts} Hty Hty₁ Hty₂ Hc) H∉ = ∉⋃' (fv ∘ ts)
  $ Fin-cases (∉-dom-fv Hty H∉)
  $ Fin-cases (∉-dom-fv Hty₁ H∉)
  $ Fin-cases (∉-dom-fv Hty₂ H∉) λ ()
∉-dom-fv (tsolve {ts = ts} Hty Hty₁ Hty₂ Hc) H∉ = ∉⋃' (fv ∘ ts)
  $ Fin-cases (∉-dom-fv Hty H∉)
  $ Fin-cases (∉-dom-fv Hty₁ H∉)
  $ Fin-cases (∉-dom-fv Hty₂ H∉) λ ()

well-typed→lc : Γ ⊢ t ∶ T → lc-at 0 t
well-typed→lc (tsub Hty _)               = well-typed→lc Hty
well-typed→lc (tpromote Hty _ _ _)       = well-typed→lc Hty
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
well-typed→lc (tdiff Hty Hty₁ Hty₂ Hc) = lc-at-op
  $ Fin-cases (well-typed→lc Hty)
  $ Fin-cases (well-typed→lc Hty₁)
  $ Fin-cases (well-typed→lc Hty₂) λ ()
well-typed→lc (tsolve Hty Hty₁ Hty₂ Hc) = lc-at-op
  $ Fin-cases (well-typed→lc Hty)
  $ Fin-cases (well-typed→lc Hty₁)
  $ Fin-cases (well-typed→lc Hty₂) λ ()

weaken-typing : Γ ⊢ t ∶ T → Γ ⊆ Γ' → Γ' ⊢ t ∶ T
weaken-typing (tsub Hty H<:) H⊆           = tsub (weaken-typing Hty H⊆) H<:
weaken-typing (tpromote Hty H≤ H~ H⊆') H⊆ = tpromote Hty H≤ H~ (env-sub-trans H⊆' H⊆)
weaken-typing (tvar H∈) H⊆                = tvar (env-sub-trans H∈ H⊆)
weaken-typing {Γ' = Γ'} (tlam (Иi As Hty)) H⊆ = tlam $ Иi (As ∪ dom Γ') λ a →
  weaken-typing (Hty a ⦃ ∉∪₁ auto ⦄) (sub-cons' (∉∪₂ As auto) H⊆)
weaken-typing (tapp Hty Hty₁) H⊆ =
  tapp (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆)
weaken-typing (tprim Hϕ Hty) H⊆         = tprim Hϕ (weaken-typing Hty H⊆)
weaken-typing treal H⊆                  = treal
weaken-typing (ttup Htys) H⊆            = ttup λ i → weaken-typing (Htys i) H⊆
weaken-typing (tproj i Hty) H⊆          = tproj i (weaken-typing Hty H⊆)
weaken-typing (tif Hty Hty₁ Hty₂ H≤) H⊆ =
  tif (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) (weaken-typing Hty₂ H⊆) H≤
weaken-typing (tdiff Hty Hty₁ Hty₂ Hc) H⊆ =
  tdiff (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) (weaken-typing Hty₂ H⊆) Hc
weaken-typing (tsolve Hty Hty₁ Hty₂ Hc) H⊆ =
  tsolve (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) (weaken-typing Hty₂ H⊆) Hc

tlam-inv :
  {T₀ T₁ T₂ : Ty}
  {t : Tm ^ 1}
  (_ : Γ ⊢ lam T₀ ▹ t ∶ T)
  (_ : T ≡ᵢ T₁ ⇒[ X ] T₂)
  → ----------------------------------------------------------------------
  Σ[ T₁' ∈ Ty ] (T₁ <: T₁') × (И[ a ∈ 𝔸 ] Γ , a ∶ T₁' ⊢ conc (t ₀) a ∶ T₂)
tlam-inv (tlam Hlam) reflᵢ                        = _ , tsub-refl , Hlam
tlam-inv {Γ} (tsub Hty (sarr H<:₁ Hc H<:₂)) reflᵢ =
  let T₁' , H<:' , Иi As Hlam = tlam-inv Hty reflᵢ
  in  T₁' , tsub-trans H<:₁ H<:' , Иi As λ a → tsub (Hlam a) H<:₂
tlam-inv {Γ} (tpromote {T = _ ⇒[ _ ] _} Hty H≤ H~ H⊆) reflᵢ =
  let T₁' , H<: , Иi As Hlam = tlam-inv Hty reflᵢ
  in  T₁' , H<: , Иi (As ∪ dom Γ) λ a ⦃ H∉ ⦄ →
    weaken-typing (Hlam a ⦃ ∉∪₁ H∉ ⦄) (sub-cons' (∉∪₂ As H∉) H⊆)

ttup-inv :
  {vs : Tm ^ n}
  {Ts : Ty ^ n}
  (_ : Γ ⊢ tup n ▹ vs ∶ T)
  (_ : T ≡ᵢ ttup n Ts)
  → ---------------------------
  ∀ i → Γ ⊢ vs i ∶ Ts i
ttup-inv (ttup Htys) Heq i = subst (_ ⊢ _ ∶_)
  (is-set→cast-pathp (Ty ^_) Nat-is-set (ap snd (ttup-inj (Id≃path.to Heq))) $ₚ i)
  (Htys i)
ttup-inv (tsub Hty (stup H<:)) reflᵢ i = tsub (ttup-inv Hty reflᵢ i) (H<: i)
ttup-inv (tpromote {T = ttup _ _} Hty H≤ H~ H⊆) reflᵢ i =
  tpromote (ttup-inv Hty reflᵢ i) H≤ (H~ i) H⊆

subst-pres-typing :
  {x : 𝔸}
  {t u : Tm}
  {T₁ T₂ : Ty}
  (_ : Γ' ≡ᵢ [ x ∶ T₂ ] & Γ)
  (_ : ε ⊢ u ∶ T₂)
  (_ : Γ' ⊢ t ∶ T₁)
  → --------------------------
  Γ ⊢ (x => u) t ∶ T₁
subst-pres-typing {Γ = Γ} {x = x} reflᵢ Hu (tvar {a = a} H∈) with x ≡? a
... | yes x≡a with sub-cons _ ←
  env-sub-strengthenr {Γ₂' = Γ} H∈ (λ a' → subst (a' ∈ᶠˢ_) (sym $ ap [_] x≡a)) =
  weaken-typing Hu sub-nil'
... | no x≠a = tvar $ env-sub-strengthenl H∈ λ _ H∈' → false→is-no $
  ∈ᶠˢ-split (λ where reflᵢ → ∈ᶠˢ-split (λ where reflᵢ → x≠a refl) ¬mem-[] H∈') ¬mem-[]
subst-pres-typing {Γ = Γ} {x = x} {u = u} {T₂ = T₂} reflᵢ Hu
  (tlam {T = T} {T'} {t = t} (Иi As Hty)) = tlam $ Иi ([ x ] ∪ As) λ a ⦃ H∉ ⦄ →
  let Heq : (x => u)((0 ~> a) (t ₀)) ≡ (0 ~> a)((x => u) (t ₀))
      Heq = subst-open-comm (t ₀) (sym≠ a x (∉∷₁ H∉)) (lc-at→≻ _ _ $ well-typed→lc Hu)
  in subst (λ x → _ ⊢ x ∶ _) Heq
     $ subst-pres-typing (Id≃path.from (&-cons-distr {Γ' = Γ})) Hu (Hty a ⦃ ∉∷₂ H∉ ⦄)
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
subst-pres-typing HΓ Hu (tdiff Hty Hty₁ Hty₂ Hc) = tdiff
  (subst-pres-typing HΓ Hu Hty)
  (subst-pres-typing HΓ Hu Hty₁)
  (subst-pres-typing HΓ Hu Hty₂)
  Hc
subst-pres-typing HΓ Hu (tsolve Hty Hty₁ Hty₂ Hc) = tsolve
  (subst-pres-typing HΓ Hu Hty)
  (subst-pres-typing HΓ Hu Hty₁)
  (subst-pres-typing HΓ Hu Hty₂)
  Hc
subst-pres-typing HΓ Hu (tsub Hty H<:) = tsub (subst-pres-typing HΓ Hu Hty) H<:
subst-pres-typing {Γ = Γ} {x = x} reflᵢ Hu
  (tpromote {Γ = Γ'} Hty H≤ H~ H⊆) with holds? (x ∈ dom Γ')
... | yes H∈ with Γ'' , p , H⊆' , Hdisj ←
  env-sub-&-diffl {Γ₂' = Γ}
    (λ _ → ∈ᶠˢ-split (λ where reflᵢ → H∈) (λ Hε → absurd (¬mem-[] Hε))) H⊆
  rewrite Id≃path.from p = tpromote
    (subst-pres-typing reflᵢ Hu Hty)
    (λ H∈ → H≤ (env-sub-trans H∈ (env-sub-weakenl env-sub-refl Hdisj)))
    H~
    H⊆'
... | no H∉ = tpromote
  (subst (_ ⊢_∶ _) (sym $ subst-fresh _ _ (∉-dom-fv Hty (false→is-no H∉))) Hty)
  H≤
  H~
  (env-sub-strengthenl H⊆ λ _ H∈ →
    false→is-no $ ∈ᶠˢ-split (λ where reflᵢ → H∉ H∈) ¬mem-[])
