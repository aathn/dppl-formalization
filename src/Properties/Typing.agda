open import Lib.Reals
module Properties.Typing (R : Reals₀) where

open Reals R hiding (refl)

-- Lemmas purely about typing

open import Syntax R
open import Typing R
open import Properties.Util

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.LocalClosedness
open import Lib.Freshness
open import Lib.FunExt
open import Lib.AbstractionConcretion hiding (abs)
open import Lib.BindingSignature
open import Lib.Substitution

open import Data.List using (_++_)
open import Data.List.Properties using (++-conicalʳ)
open import Data.List.Relation.Binary.Sublist.Propositional
  using (_⊆_ ; [] ; _∷_ ; _∷ʳ_ ; ⊆-refl ; ⊆-trans ; lookup)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties as SP using ()
open import Data.List.Relation.Binary.Pointwise as P using (Pointwise ; [] ; _∷_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Relation.Unary.Any.Properties as AnyP using ()
open import Data.List.Relation.Unary.All as A using (All ; [] ; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)

infixl 5 _&_
_&_ : TyEnv → TyEnv → TyEnv
Γ & Γ′ = Γ′ ++ Γ

sub-refl : {T : Type} → T <: T
sub-refl {treal c} = sreal ≤refl
sub-refl {T ⇒[ x ] T₁} = sarr sub-refl sub-refl ≤refl
sub-refl {ttup ts} = stup (λ i → sub-refl)
sub-refl {tdist T} = sdist sub-refl

sub-trans : {T₁ T₂ T₃ : Type} → T₁ <: T₂ → T₂ <: T₃ → T₁ <: T₃
sub-trans (sreal H≤) (sreal H≤′) = sreal (≤trans H≤′ H≤)
sub-trans (stup Hsubs) (stup Hsubs′) = stup (λ i → sub-trans (Hsubs i) (Hsubs′ i))
sub-trans (sarr Hsub1 Hsub4 H≤) (sarr Hsub2 Hsub3 H≤′) =
  sarr (sub-trans Hsub2 Hsub1) (sub-trans Hsub4 Hsub3) (≤trans H≤ H≤′)
sub-trans (sdist Hsub1) (sdist Hsub2) = sdist (sub-trans Hsub1 Hsub2)

sub-⊆ :
  {Γ₁ Γ₂ Γ₁′ : TyEnv}
  (_ : Γ₂ <:ᴱ Γ₁)
  (_ : Γ₁′ ⊆ Γ₁)
  → ------------------------------
  ∃ λ Γ₂′ → Γ₂′ <:ᴱ Γ₁′ × Γ₂′ ⊆ Γ₂
sub-⊆ [] [] = [] , [] , []
sub-⊆ (Hsub ∷ Hsubs) (y ∷ʳ H⊆) =
  let Γ₂′ , Hsub′ , H⊆′ = sub-⊆ Hsubs H⊆
  in  Γ₂′ , Hsub′ , _ ∷ʳ H⊆′
sub-⊆ (Hsub ∷ Hsubs) (refl ∷ H⊆) =
  let Γ₂′ , Hsub′ , H⊆′ = sub-⊆ Hsubs H⊆
  in  _ ∷ Γ₂′ , Hsub ∷ Hsub′ , refl ∷ H⊆′

sub-dom :
  {Γ₁ Γ₂ : TyEnv}
  (_ : Γ₁ <:ᴱ Γ₂)
  → -------------
  dom Γ₁ ≡ dom Γ₂
sub-dom [] = refl
sub-dom (x≡y ∷ Hsub) = ap₂ _∪_ (ap [_] $ π₁ x≡y) (sub-dom Hsub)

dom-distinct :
  {Γ₁ Γ₂ : TyEnv}
  (_ : dom Γ₁ ≡ dom Γ₂)
  → -----------------------
  Distinct Γ₁ → Distinct Γ₂
dom-distinct {Γ₂ = []} Hdom [] = []
dom-distinct {Γ₂ = (y , T) ∷ Γ₂} Hdom (H∉ ∷ Hd) with refl ← ∪inj₁ Hdom =
  subst (y ∉_) (∪inj₂ Hdom) H∉ ∷ dom-distinct (∪inj₂ Hdom) Hd

≤ᶜ-<:-trans :
  {c : Coeff}
  {T₁ T₂ : Type}
  (_ : c ≤ᶜ T₁)
  (_ : T₂ <: T₁)
  → ------------
  c ≤ᶜ T₂
≤ᶜ-<:-trans H≤ (sreal H≤′) = ≤trans H≤ H≤′
≤ᶜ-<:-trans H≤ (stup Hsubs) i = ≤ᶜ-<:-trans (H≤ i) (Hsubs i)
≤ᶜ-<:-trans H≤ (sarr _ _ _) = tt
≤ᶜ-<:-trans H≤ (sdist _) = tt

≤ᴱ-<:ᴱ-trans :
  {c : Coeff}
  {Γ₁ Γ₂ : TyEnv}
  (_ : c ≤ᴱ Γ₁)
  (_ : Γ₂ <:ᴱ Γ₁)
  → -------------
  c ≤ᴱ Γ₂
≤ᴱ-<:ᴱ-trans [] [] = []
≤ᴱ-<:ᴱ-trans (H≤ ∷ H≤′) ((_ , Hsub) ∷ Hsub′) =
  ≤ᶜ-<:-trans H≤ Hsub ∷ ≤ᴱ-<:ᴱ-trans H≤′ Hsub′

sub-env :
  {Γ₁ Γ₂ : TyEnv}
  {t : Term}
  {e : Eff}
  {T : Type}
  (_ : Γ₁ ⊢ t :[ e ] T)
  (_ : Γ₂ <:ᴱ Γ₁)
  → -------------------
  Γ₂ ⊢ t :[ e ] T
sub-env (tvar H⊆ Hd) Hsub
  with Γ₂′ , (refl , Hsub′) ∷ [] , H⊆′ ← sub-⊆ Hsub H⊆ =
  tsub (tvar H⊆′ (dom-distinct (symm $ sub-dom Hsub) Hd)) ≤refl Hsub′
sub-env (tabs (Иi As Hcof)) Hsub =
  tabs $ Иi As λ y → sub-env (Hcof y) ((refl , sub-refl) ∷ Hsub)
sub-env (tapp Htype Htype₁) Hsub =
  tapp (sub-env Htype Hsub) (sub-env Htype₁ Hsub)
sub-env (tprim Hϕ Hd Htypes) Hsub =
  tprim Hϕ (dom-distinct (symm $ sub-dom Hsub) Hd) (λ i → sub-env (Htypes i) Hsub)
sub-env (treal Hd) Hsub = treal (dom-distinct (symm $ sub-dom Hsub) Hd)
sub-env (ttup Hd Htypes) Hsub =
  ttup (dom-distinct (symm $ sub-dom Hsub) Hd) (λ i → sub-env (Htypes i) Hsub)
sub-env (tproj i Htype) Hsub = tproj i (sub-env Htype Hsub)
sub-env (tif Htype Htype₁ Htype₂) Hsub =
  tif (sub-env Htype Hsub) (sub-env Htype₁ Hsub) (sub-env Htype₂ Hsub)
sub-env (tdiff Hc Htype Htype₁) Hsub =
  tdiff Hc (sub-env Htype Hsub) (sub-env Htype₁ Hsub)
sub-env (tsolve Htype Htype₁ Htype₂) Hsub =
  tsolve (sub-env Htype Hsub) (sub-env Htype₁ Hsub) (sub-env Htype₂ Hsub)
sub-env (tdist HD Hd Htypes) Hsub =
  tdist HD (dom-distinct (symm $ sub-dom Hsub) Hd) (λ i → sub-env (Htypes i) Hsub)
sub-env (tassume Htype) Hsub = tassume (sub-env Htype Hsub)
sub-env (tweight Htype) Hsub = tweight (sub-env Htype Hsub)
sub-env (texpect Htype) Hsub = texpect (sub-env Htype Hsub)
sub-env (tinfer Htype) Hsub  = tinfer (sub-env Htype Hsub)
sub-env (tsub Htype H≤ Hsub′) Hsub = tsub (sub-env Htype Hsub) H≤ Hsub′
sub-env (tpromote Htype H≤ H⊆ Hd) Hsub =
  let Γ₂′ , Hsub′ , H⊆′ = sub-⊆ Hsub H⊆ in
  tpromote
    (sub-env Htype Hsub′)
    (≤ᴱ-<:ᴱ-trans H≤ Hsub′)
    H⊆′
    (dom-distinct (symm $ sub-dom Hsub) Hd)

well-typed-distinct :
  {Γ : TyEnv}
  {t : Term}
  {e : Eff}
  {T : Type}
  → -------------------------
  Γ ⊢ t :[ e ] T → Distinct Γ

well-typed-distinct (tvar _ Hd) = Hd
well-typed-distinct (tabs (Иi As Hcof))
  with x , x∉As ← fresh As
  with _ ∷ Hd ← well-typed-distinct (Hcof x {{x∉As}}) = Hd
well-typed-distinct (tapp Htype Htype₁) = well-typed-distinct Htype
well-typed-distinct (tprim Hϕ Hd Htypes) = Hd
well-typed-distinct (treal Hd) = Hd
well-typed-distinct (ttup Hd Htypes) = Hd
well-typed-distinct (tproj i Htype) = well-typed-distinct Htype
well-typed-distinct (tif Htype Htype₁ Htype₂) = well-typed-distinct Htype
well-typed-distinct (tdiff _ Htype Htype₁) = well-typed-distinct Htype
well-typed-distinct (tsolve Htype Htype₁ Htype₂) = well-typed-distinct Htype
well-typed-distinct (tdist HD Hd Htypes) = Hd
well-typed-distinct (tassume Htype) = well-typed-distinct Htype
well-typed-distinct (tweight Htype) = well-typed-distinct Htype
well-typed-distinct (texpect Htype) = well-typed-distinct Htype
well-typed-distinct (tinfer Htype)  = well-typed-distinct Htype
well-typed-distinct (tsub Htype _ _) = well-typed-distinct Htype
well-typed-distinct (tpromote _ _ _ Hd) = Hd

weaken-typing :
  {Γ Γ′ : TyEnv}
  {t : Term}
  {e : Eff}
  {T : Type}
  (_ : Γ′ ⊢ t :[ e ] T)
  (_ : Γ′ ⊆ Γ)
  (_ : Distinct Γ)
  → -------------------
  Γ ⊢ t :[ e ] T
weaken-typing (tvar H⊆₀ _) H⊆ Hd = tvar (⊆-trans H⊆₀ H⊆) Hd
weaken-typing {Γ} (tabs (Иi As Htype)) H⊆ Hd =
  tabs $ Иi (dom Γ ∪ As) λ
    {x {{∉∪}} → weaken-typing (Htype x) (refl ∷ H⊆) (it ∷ Hd)}
weaken-typing (tapp Htype Htype₁) H⊆ Hd =
  tapp (weaken-typing Htype H⊆ Hd) (weaken-typing Htype₁ H⊆ Hd)
weaken-typing (tprim Hϕ _ Htypes) H⊆ Hd =
  tprim Hϕ Hd λ i → weaken-typing (Htypes i) H⊆ Hd
weaken-typing (treal _) _ Hd = treal Hd
weaken-typing (ttup _ Htypes) H⊆ Hd =
  ttup Hd λ i → weaken-typing (Htypes i) H⊆ Hd
weaken-typing (tproj i Htype) H⊆ Hd =
  tproj i (weaken-typing Htype H⊆ Hd)
weaken-typing (tif Htype Htype₁ Htype₂) H⊆ Hd =
  tif
    (weaken-typing Htype H⊆ Hd)
    (weaken-typing Htype₁ H⊆ Hd)
    (weaken-typing Htype₂ H⊆ Hd)
weaken-typing (tdiff Hcs Htype Htype₁) H⊆ Hd =
  tdiff Hcs
    (weaken-typing Htype H⊆ Hd)
    (weaken-typing Htype₁ H⊆ Hd)
weaken-typing (tsolve Htype Htype₁ Htype₂) H⊆ Hd =
  tsolve
    (weaken-typing Htype H⊆ Hd)
    (weaken-typing Htype₁ H⊆ Hd)
    (weaken-typing Htype₂ H⊆ Hd)
weaken-typing (tdist HD _ Htypes) H⊆ Hd =
  tdist HD Hd λ i → weaken-typing (Htypes i) H⊆ Hd
weaken-typing (tassume Htype) H⊆ Hd = tassume (weaken-typing Htype H⊆ Hd)
weaken-typing (tweight Htype) H⊆ Hd = tweight (weaken-typing Htype H⊆ Hd)
weaken-typing (texpect Htype) H⊆ Hd = texpect (weaken-typing Htype H⊆ Hd)
weaken-typing (tinfer Htype) H⊆ Hd = tinfer (weaken-typing Htype H⊆ Hd)
weaken-typing (tsub Htype H≤ Hsub) H⊆ Hd =
  tsub (weaken-typing Htype H⊆ Hd) H≤ Hsub
weaken-typing (tpromote Htype H≤ H⊆₀ _) H⊆ Hd =
  tpromote Htype H≤ (⊆-trans H⊆₀ H⊆) Hd


tabs-inv :
  ∀ {Γ T₀ t e T e′ T₁ T₂}
  → Γ ⊢ abs T₀ t :[ e ] T
  → T ≡ T₁ ⇒[ e′ ] T₂
  → ----------------------------------------------
    И x ∶ 𝔸 , Γ , x ∶ T₁ ⊢ conc (t ₀) x :[ e′ ] T₂
tabs-inv (tabs Habs) refl = Habs
tabs-inv (tsub Htype H≤ (sarr Hsub₀ Hsub₁ He)) refl
  with Иi As Hcof ← tabs-inv Htype refl =
  Иi As λ x → sub-env (tsub (Hcof x) He Hsub₁) ((refl , Hsub₀) ∷ P.refl (refl , sub-refl))
tabs-inv (tpromote {Γ} {T = _ ⇒[ _ ] _} Htype H≤ H⊆ Hd) refl
  with Иi As Hcof ← tabs-inv Htype refl =
  Иi (dom Γ ∪ As) λ { x {{∉∪}} → weaken-typing (Hcof x) (refl ∷ H⊆) (it ∷ Hd) }

ttup-inv :
  {n : ℕ}
  {Γ : TyEnv}
  {vs : Vector Term n}
  {e : Eff}
  {T : Type}
  {Ts : Vector Type n}
  (_ : Γ ⊢ tup vs :[ e ] T)
  (_ : T ≡ ttup Ts)
  → ------------------------
  ∀ i → Γ ⊢ vs i :[ e ] Ts i
ttup-inv (ttup _ Hvs) refl = Hvs
ttup-inv (tsub Htype H≤ (stup Hsubs)) refl = λ i →
  tsub (ttup-inv Htype refl i) H≤ (Hsubs i)
ttup-inv (tpromote {T = ttup _} Htype H≤ H⊆ Hd) refl = λ i →
  tpromote (ttup-inv Htype refl i) H≤ H⊆ Hd

texpect-inv :
  {Γ : TyEnv}
  {D : Dist}
  {rs : Vector ℝ (DistAr D)}
  {e : Eff}
  {T T′ : Type}
  (_ : Γ ⊢ dist D (real ∘ rs) :[ e ] T)
  (_ : T ≡ tdist T′)
  → -----------------------------------------------
  ∃ λ cs → ∃ λ T″ → DistTy D ≡ (cs , T″) × T″ <: T′
texpect-inv (tdist HD _ _) refl = _ , _ , HD , sub-refl
texpect-inv (tsub Htype H≤ (sdist Hsub)) refl with texpect-inv Htype refl
... | _ , _ , Heq , Hsub′ = _ , _ , Heq , sub-trans Hsub′ Hsub
texpect-inv (tpromote {T = tdist _} Htype H≤ H⊆ Hd) refl =
  texpect-inv Htype refl

tinfer-inv :
  {Γ : TyEnv}
  {v : Vector Term 1}
  {e : Eff}
  {T T′ : Type}
  (_ : Γ ⊢ infer v :[ e ] T)
  (_ : T ≡ tdist T′)
  → ------------------------------
  Γ ⊢ v ₀ :[ e ] tunit ⇒[ rnd ] T′
tinfer-inv (tinfer Htype) refl = Htype
tinfer-inv (tsub Htype H≤ (sdist Hsub)) refl =
  tsub (tinfer-inv Htype refl) H≤ (sarr sub-refl Hsub ≤refl)
tinfer-inv (tpromote {T = tdist _} Htype H≤ H⊆ Hd) refl =
  tpromote (tinfer-inv Htype refl) H≤ H⊆ Hd

dom-∈ : {Γ : TyEnv}{x : 𝔸} → x ∈ dom Γ → ∃ λ T → (x , T) ∈ˡ Γ
dom-∈ {x ∷ Γ} (∈∪₁ ∈[]) = _ , here refl
dom-∈ {x ∷ Γ} (∈∪₂ x∈Γ) with T , H∈ ← dom-∈ x∈Γ = T , there H∈

∈-dom : {Γ : TyEnv}{x : 𝔸}{T : Type} → (x , T) ∈ˡ Γ → x ∈ dom Γ
∈-dom {x ∷ Γ} (here refl) = ∈∪₁ ∈[]
∈-dom {x ∷ Γ} (there H∈)  = ∈∪₂ (∈-dom H∈)

∉-dom-⊆ : {Δ Γ : TyEnv}{x : 𝔸} → x ∉ dom Γ → Δ ⊆ Γ → x ∉ dom Δ
∉-dom-⊆ {[]} H∉ H⊆ = ∉Ø
∉-dom-⊆ {_ ∷ Δ} ∉∪ (_ ∷ʳ H⊆) = ∉-dom-⊆ it H⊆
∉-dom-⊆ {y ∷ Δ} (∉∪ {{p}}) (refl ∷ H⊆) = ∉∪ {{p = p}} {{∉-dom-⊆ it H⊆}}

∉-dom-fv :
  {x : 𝔸}
  {Γ : TyEnv}
  {t : Term}
  {e : Eff}
  {T : Type}
  (_ : Γ ⊢ t :[ e ] T)
  (_ : x ∉ dom Γ)
  → ------------------
  x ∉ fv t
∉-dom-fv (tvar H⊆ Hd) H∉ with ∉∪ {{p}} ← ∉-dom-⊆ H∉ H⊆ = p
∉-dom-fv {x} (tabs {t = t} (Иi As Hcof)) H∉
  with y , ∉∪ {{∉[]}} ← fresh {𝔸} ([ x ] ∪ As)
  with Hnin ← ∉-dom-fv {x} (Hcof y) (∉∪ {{p = ∉[] {{p = symm≠ y x it}}}} {{H∉}}) =
  ∉∪ {{p = open-notin (t ₀) Hnin}}
∉-dom-fv (tapp Htype Htype₁) H∉ =
  ∉∪ {{p = ∉-dom-fv Htype H∉}} {{∉∪ {{p = ∉-dom-fv Htype₁ H∉}}}}
∉-dom-fv (tprim _ _ Htypes) H∉ = ∉⋃′ _ λ i → ∉-dom-fv (Htypes i) H∉
∉-dom-fv (treal Hd) H∉ = ∉Ø
∉-dom-fv (ttup _ Htypes) H∉ = ∉⋃′ _ λ i → ∉-dom-fv (Htypes i) H∉
∉-dom-fv (tproj i Htype) H∉ = ∉∪ {{p = ∉-dom-fv Htype H∉}}
∉-dom-fv (tif Htype Htype₁ Htype₂) H∉ =
  ∉∪ {{p = ∉-dom-fv Htype H∉}}
    {{∉∪ {{p = ∉-dom-fv Htype₁ H∉}}
      {{∉∪ {{p = ∉-dom-fv Htype₂ H∉}} }} }}
∉-dom-fv (tdiff _ Htype Htype₁) H∉ =
  ∉∪ {{p = ∉-dom-fv Htype H∉}} {{∉∪ {{p = ∉-dom-fv Htype₁ H∉}}}}
∉-dom-fv (tsolve Htype Htype₁ Htype₂) H∉ =
  ∉∪ {{p = ∉-dom-fv Htype H∉}}
    {{∉∪ {{p = ∉-dom-fv Htype₁ H∉}}
      {{∉∪ {{p = ∉-dom-fv Htype₂ H∉}} }} }}
∉-dom-fv (tdist _ _ Htypes) H∉ = ∉⋃′ _ λ i → ∉-dom-fv (Htypes i) H∉
∉-dom-fv (tassume Htype) H∉ = ∉∪ {{p = ∉-dom-fv Htype H∉}}
∉-dom-fv (tweight Htype) H∉ = ∉∪ {{p = ∉-dom-fv Htype H∉}}
∉-dom-fv (texpect Htype) H∉ = ∉∪ {{p = ∉-dom-fv Htype H∉}}
∉-dom-fv (tinfer Htype) H∉  = ∉∪ {{p = ∉-dom-fv Htype H∉}}
∉-dom-fv (tsub Htype _ _) H∉ = ∉-dom-fv Htype H∉
∉-dom-fv (tpromote Htype H≤ H⊆ Hd) H∉ = ∉-dom-fv Htype (∉-dom-⊆ H∉ H⊆)

&-dom : {Γ : TyEnv}{x : 𝔸}(Γ′ : TyEnv) → x ∉ dom (Γ & Γ′) → x ∉ dom Γ′ ∪ dom Γ
&-dom [] H∉ = ∉∪ {{q = H∉}}
&-dom ((y , T) ∷ Γ′) (∉∪ {{p = H∉₁}} {{H∉₂}}) with ∉∪ ← &-dom Γ′ H∉₂ =
  ∉∪ {{p = ∉∪ {{p = H∉₁}}}}

dom-& : {Γ′ Γ : TyEnv} {x : 𝔸} → x ∉ dom Γ′ ∪ dom Γ → x ∉ dom (Γ & Γ′)
dom-& {[]} ∉∪ = it
dom-& {_ ∷ Γ′} {Γ} {x} (∉∪ {{∉∪ {{p = H∉}}}}) = ∉∪ {{p = H∉}} {{dom-& it}}

distinct-weaken :
  {Γ′ Γ : TyEnv}
  {x : 𝔸}
  {T : Type}
  → -------------------------------------------
  Distinct (Γ , x ∶ T & Γ′) → Distinct (Γ & Γ′)
distinct-weaken {[]} (x ∷ Hd) = Hd
distinct-weaken {Γ′ , x′ ∶ T′} {Γ} {x} {T} (H∉ ∷ Hd)
  with ∉∪ {{q = ∉∪}} ← &-dom Γ′ H∉ =
  dom-& it ∷ distinct-weaken Hd

⊆-strengthen :
  {Γ₂ Γ₁ Γ : TyEnv}
  {x : 𝔸}
  {T : Type}
  (_ : x ∉ dom Γ)
  (_ : Γ ⊆ Γ₁ , x ∶ T & Γ₂)
  → -----------------------
  Γ ⊆ Γ₁ & Γ₂
⊆-strengthen {[]} H∉ (.(_ , _) ∷ʳ H⊆) = H⊆
⊆-strengthen {[]} {x = x} (∉∪ {{∉[]}}) (refl ∷ H⊆) with () ← ¬≠ x it
⊆-strengthen {x ∷ Γ₂} H∉ (.x ∷ʳ H⊆) = x ∷ʳ (⊆-strengthen H∉ H⊆)
⊆-strengthen {x ∷ Γ₂} ∉∪ (x₁ ∷ H⊆) = x₁ ∷ (⊆-strengthen it H⊆)

⊆-dom :
  {Δ Γ : TyEnv}
  {x : 𝔸}
  (_ : Γ ⊆ Δ)
  (_ : x ∉ dom Δ)
  → -------------
  x ∉ dom Γ
⊆-dom [] ∉Ø = ∉Ø
⊆-dom {Δ , y ∶ _} (_ ∷ʳ Hsub) ∉∪ = ⊆-dom Hsub it
⊆-dom {Δ , _ ∶ _} {Γ , _ ∶ _} {x} (refl ∷ Hsub) (∉∪ {{H∉}}) =
  ∉∪ {{p = H∉}} {{⊆-dom Hsub it}}

⊆-distinct :
  {Δ Γ : TyEnv}
  (_ : Distinct Γ)
  (_ : Δ ⊆ Γ)
  → --------------
  Distinct Δ
⊆-distinct {[]} Hd H⊆ = []
⊆-distinct {_ ∷ Δ} (_ ∷ Hd) (_ ∷ʳ H⊆) = ⊆-distinct Hd H⊆
⊆-distinct {x ∷ Δ} (H∉ ∷ Hd) (refl ∷ H⊆) =
  ⊆-dom H⊆ H∉ ∷ ⊆-distinct Hd H⊆

⊆-split :
  {Γ₂ Γ₁ Δ : TyEnv}
  {x : 𝔸}
  {T : Type}
  (_ : x ∉ dom Γ₁ ∪ dom Γ₂)
  (_ : x ∈ dom Δ)
  (_ : Δ ⊆ Γ₁ , x ∶ T & Γ₂)
  → -------------------------------------------------------
  ∃ λ Δ₁ → ∃ λ Δ₂ → Δ₁ ⊆ Γ₁ × Δ₂ ⊆ Γ₂ × Δ ≡ Δ₁ , x ∶ T & Δ₂

⊆-split {[]} ∉∪ H∈ (.(_ , _) ∷ʳ Hsub) with _ , H∈′ ← dom-∈ H∈
  with () ← ∉→¬∈ (∈-dom $ lookup Hsub H∈′)
⊆-split {[]} ∉∪ H∈ (refl ∷ Hsub) = _ , _ , Hsub , [] , refl
⊆-split {x ∷ Γ₂} (∉∪ {{q = ∉∪}}) H∈ (.x ∷ʳ Hsub)
  with  Δ₁ , Δ₂ , Hsub1 , Hsub2 , Heq ← ⊆-split ∉∪ H∈ Hsub =
  Δ₁ , Δ₂ , Hsub1 , x ∷ʳ Hsub2 , Heq
⊆-split {x ∷ Γ₂} (∉∪ {{ q = ∉∪ }}) (∈∪₂ H∈) (refl ∷ Hsub)
  with Δ₁ , Δ₂ , Hsub1 , Hsub2 , refl ← ⊆-split ∉∪ H∈ Hsub =
  Δ₁ , x ∷ Δ₂ , Hsub1 , refl ∷ Hsub2 , refl
⊆-split {Γ₂ , x ∶ _} (∉∪ {{ q = ∉∪ {{ p = ∉[] }} }}) (∈∪₁ ∈[]) (refl ∷ Hsub)
  with () ← ¬≠ x it

distinct-∉ :
  {Γ₂ Γ₁ : TyEnv}
  {x : 𝔸}
  {T : Type}
  → ----------------------------------------------
  Distinct (Γ₁ , x ∶ T & Γ₂) → x ∉ dom Γ₁ ∪ dom Γ₂
distinct-∉ {[]} {Γ₁} {x} (H∉ ∷ _) = ∉∪ {{p = H∉}}
distinct-∉ {(y , _) ∷ Γ₂} {Γ₁} {x} {T} (H∉ ∷ Hd)
  with ∉∪ {{q = ∉∪ {{∉[]}}}} ← &-dom Γ₂ H∉ | ∉∪ ← distinct-∉ Hd = it
  where instance
  _ : x ≠ y
  _ = symm≠ y x it

all-weaken :
  {A : Set}
  {P : A → Set}
  {l₁ l₂ : List A}
  {x : A}
  → -------------------------------------
  All P (l₁ ++ x ∷ l₂) → All P (l₁ ++ l₂)
all-weaken {l₁ = []} (px ∷ Hall) = Hall
all-weaken {l₁ = x ∷ l₁} (px ∷ Hall) = px ∷ all-weaken Hall

open LocalClosed
open Body

well-typed-lc :
  {Γ : TyEnv}
  {t : Term}
  {e : Eff}
  {T : Type}
  → ------------------------
  Γ ⊢ t :[ e ] T → lc-at 0 t
well-typed-lc (tvar _ _) = lc-at-fvar
well-typed-lc (tabs {t = t} (Иi As Hcof)) = lc-at-op λ
  { ₀ → let Hbody : body (t ₀)
            Hbody = Иi As λ x → lc-at→≻ _ _ $ well-typed-lc (Hcof x)
        in ≻→lc-at _ _ $ body→1≻ _ Hbody
  }
well-typed-lc (tapp Htype Htype₁) = lc-at-op λ
  { ₀ → well-typed-lc Htype
  ; ₁ → well-typed-lc Htype₁
  }
well-typed-lc (tprim _ _ Htypes) = lc-at-op $ well-typed-lc ∘ Htypes
well-typed-lc (treal _)          = lc-at-op λ()
well-typed-lc (ttup _ Htypes)    = lc-at-op $ well-typed-lc ∘ Htypes
well-typed-lc (tproj i Htype)    = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tif Htype Htype₁ Htype₂) = lc-at-op λ
  { ₀ → well-typed-lc Htype
  ; ₁ → well-typed-lc Htype₁
  ; ₂ → well-typed-lc Htype₂
  }
well-typed-lc (tdiff _ Htype Htype₁) = lc-at-op λ
  { ₀ → well-typed-lc Htype
  ; ₁ → well-typed-lc Htype₁
  }
well-typed-lc (tsolve Htype Htype₁ Htype₂) = lc-at-op λ
  { ₀ → well-typed-lc Htype
  ; ₁ → well-typed-lc Htype₁
  ; ₂ → well-typed-lc Htype₂
  }
well-typed-lc (tdist _ _ Htypes) = lc-at-op $ well-typed-lc ∘ Htypes
well-typed-lc (tassume Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tweight Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (texpect Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tinfer Htype)   = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tsub Htype _ _) = well-typed-lc Htype
well-typed-lc (tpromote Htype _ _ _) = well-typed-lc Htype

has-type-coeff-env :
  {Γ : TyEnv}
  {t : Term}
  {e : Eff}
  {T : Type}
  {c : Coeff}
  (_ : Γ ⊢ t :[ e ] T)
  (_ : c ≤ᶜ T)
  → -----------------------------------------
  ∃ λ Γ′ → Γ′ ⊢ t :[ e ] T × c ≤ᴱ Γ′ × Γ′ ⊆ Γ
has-type-coeff-env = {!!}

substitution-pres-typing :
  {Γ Γ′ : TyEnv}
  {x : 𝔸}
  {u t : Term}
  {e : Eff}
  {T₁ T₂ : Type}
  (_ : Γ , x ∶ T₂ & Γ′ ⊢ t :[ e ] T₁)
  (_ : Γ ⊢ u :[ det ] T₂)
  → ---------------------------------
  Γ & Γ′ ⊢ (x => u) t :[ e ] T₁
substitution-pres-typing {x = x} Htype Hu =
  go {{Hu = Hu}}
     {{⊆-refl}}
     {{⊆-distinct (well-typed-distinct Htype) (SP.++⁺ ⊆-refl (_ ∷ʳ ⊆-refl))}}
     Htype
  where
  go :
    {Γ Γ′ Γ″ Γ₀ : TyEnv}
    {u t : Term}
    {e : Eff}
    {T₁ T₂ : Type}
    {{_ : Γ₀ ≡ Γ , x ∶ T₂ & Γ′}}
    {{Hu : Γ″ ⊢ u :[ det ] T₂}}
    {{H⊆ : Γ ⊆ Γ″}}
    {{Hd : Distinct (Γ″ & Γ′)}}
    (_ : Γ₀ ⊢ t :[ e ] T₁)
    → ----------------------------
    Γ″ & Γ′ ⊢ (x => u) t :[ e ] T₁
  go {{refl}} (tvar {x = x₁} H⊆₀ Hd) with x ≐ x₁
  ... | equ with _ , _ , _ , _ , Heq ← ⊆-split (distinct-∉ Hd) (∈∪₁ ∈[]) H⊆₀
            with refl , refl , refl ← single-inv {{Heq}} =
        weaken-typing it (SP.++⁺ˡ _ ⊆-refl) it
  ... | neq H≢ = tvar (⊆-trans (⊆-strengthen it H⊆₀) (SP.++⁺ ⊆-refl it)) it
    where instance
    _ : x ≠ x₁
    _ = dec-neq _ _ H≢
  go {Γ′ = Γ′} {Γ″} {u = u} {{refl}} (tabs {t = t} (Иi As Hcof)) =
    tabs $ Иi (As ∪ [ x ] ∪ dom Γ′ ∪ dom Γ″) λ {y {{∉∪ {{q = ∉∪ {{H∉₁}} {{H∉₂}}}}}} →
      let Heq : (x => u)((0 ~> y) (t ₀)) ≡ (0 ~> y)((x => u) (t ₀))
          Heq = subst-open-comm (t ₀) (symm≠ y x (∉[]₁ H∉₁)) (lc-at→≻ _ _ $ well-typed-lc it)
      in
      subst (λ x → _ ⊢ x :[ _ ] _) Heq $
        go {Γ′ = Γ′ , y ∶ _} {{Hd = dom-& H∉₂ ∷ it}} (Hcof y)
    }
  go (tapp Htype Htype₁) = tapp (go Htype) (go Htype₁)
  go (tprim Hϕ _ Htypes) = tprim Hϕ it (go ∘ Htypes)
  go (treal {r = r} _) =
    subst (λ ts → _ ⊢ op (oreal r , ts) :[ _ ] _) {x = λ()}
      (funext λ ()) (treal it)
  go (ttup _ Htypes) = ttup it (go ∘ Htypes)
  go (tproj i Htype) = tproj i $ go Htype
  go (tif Htype Htype₁ Htype₂) =
    tif (go Htype) (go Htype₁) (go Htype₂)
  go (tdiff Hcs Htype Htype₁) =
    tdiff Hcs (go Htype) (go Htype₁)
  go (tsolve Htype Htype₁ Htype₂) =
    tsolve (go Htype) (go Htype₁) (go Htype₂)
  go {{refl}} (tdist HD _ Htypes) = tdist HD it (go ∘ Htypes)
  go (tassume Htype) = tassume $ go Htype
  go (tweight Htype) = tweight $ go Htype
  go (texpect Htype) = texpect $ go Htype
  go (tinfer Htype)  = tinfer  $ go Htype
  -- go {{refl}} (tweaken {Γ′ = Γ₂} {t = t} Htype H⊆ Hd) with x ∈? dom Γ₂
  -- ... | yes H∈ with Δ₁ , Δ₂ , H⊆₂ , H⊆₁ , refl ← ⊆-split (distinct-∉ Hd) H∈ H⊆ =
  --   tweaken (go Htype) (++⁺ H⊆₁ H⊆₂) (distinct-weaken Hd)
  -- ... | no H∉ rewrite subst-fresh u t (∉-dom-fv Htype (¬∈→∉ H∉)) =
  --   tweaken Htype (⊆-strengthen (¬∈→∉ H∉) H⊆) (distinct-weaken Hd)
  go (tsub Htype H≤ Hsub) = tsub (go Htype) H≤ Hsub
  go {u = u} {{refl}} {{Hu}} (tpromote {Γ′ = Γ₂} {t = t} Htype H≤ H⊆ Hd) with x ∈? dom Γ₂
  ... | yes H∈ with Δ₁ , Δ₂ , H⊆₂ , H⊆₁ , refl ← ⊆-split (distinct-∉ Hd) H∈ H⊆ =
    let Γ , Hu′ , H≤′ , H⊆′ = has-type-coeff-env Hu (A.lookup H≤ (AnyP.++⁺ʳ Δ₂ (here refl))) in
    tpromote (go {{Hu = Hu′}} {{{!!}}} {{{!!}}} Htype) {!!} {!!} it
  ... | no  H∉ rewrite subst-fresh u t (∉-dom-fv Htype (¬∈→∉ H∉)) =
    tpromote Htype H≤ (⊆-trans (⊆-strengthen (¬∈→∉ H∉) H⊆) (SP.++⁺ ⊆-refl it)) it


-- -- var-substitution-pres-typing
-- --   : ∀ {Γ Γ′ x y T₂ t e T₁}
-- --   → Γ , x ∶ T₂ & Γ′ ⊢ t :[ e ] T₁
-- --   → -------------------------------------------
-- --     Γ , y ∶ T₂ & Γ′ ⊢ (x => fvar y) t :[ e ] T₁
-- -- substitution-pres-typing {Γ′} {x} {u} {T₂} Htype Hu = go Htype
-- --   where
-- --   go
-- --     : ∀ {Γ′ Γ₀ t e T₁}
-- --     → {{Γ₀ ≡ [ x ∶ T₂ ] & Γ′}}
-- --     → Γ₀ ⊢ t :[ e ] T₁
-- --     → -------------------------
-- --       [] & Γ′ ⊢ (x => u) t :[ e ] T₁
-- --   go {{Heq}} (tvar {x = x₁})
-- --     with refl , refl , refl ← single-inv {{Heq}}
-- --     rewrite dec-equ x = Hu
-- --   go {Γ′} {{refl}} (tabs {t = t} (Иi As Hcof)) =
-- --     tabs $ Иi ([ x ] ∪ As) λ { y {{∉∪ {{∉x}}}} →
-- --       let Heq : (x => u)((0 ~> y) (t ₀)) ≡ (0 ~> y)((x => u) (t ₀))
-- --           Heq = subst-open-comm (t ₀) (symm≠ y x (∉[]₁ ∉x)) (lc-at→≻ _ _ $ well-typed-lc Hu)
-- --       in
-- --       subst (λ x → _ ⊢ x :[ _ ] _) Heq $ go {Γ′ , y ∶ _} (Hcof y)
-- --     }
-- --   go (tapp Htype Htype₁) = tapp (go Htype) (go Htype₁)
-- --   go {{refl}} (tprim Hϕ Hd Htypes) = tprim Hϕ (distinct-weaken Hd) (go ∘ Htypes)
-- --   go {Γ′} treal with () ← ++-conicalʳ Γ′ _ $ symm it
-- --   go {{refl}} (ttup Hd Htypes) = ttup (distinct-weaken Hd) (go ∘ Htypes)
-- --   go (tproj i Htype) = tproj i $ go Htype
-- --   go (tif Htype Htype₁ Htype₂) =
-- --     tif (go Htype) (go Htype₁) (go Htype₂)
-- --   go (tdiff Hcs Htype Htype₁) =
-- --     tdiff Hcs (go Htype) (go Htype₁)
-- --   go (tsolve Htype Htype₁ Htype₂) =
-- --     tsolve (go Htype) (go Htype₁) (go Htype₂)
-- --   go {{refl}} (tdist HD Hd Htypes) = tdist HD (distinct-weaken Hd) (go ∘ Htypes)
-- --   go (tassume Htype) = tassume $ go Htype
-- --   go (tweight Htype) = tweight $ go Htype
-- --   go (texpect Htype) = texpect $ go Htype
-- --   go (tinfer Htype)  = tinfer  $ go Htype
-- --   go {{refl}} (tweaken {Γ′ = Γ₂} {t = t} Htype H⊆ Hd) with x ∈? dom Γ₂
-- --   ... | yes H∈ with Δ₁ , Δ₂ , [] , H⊆₁ , refl ← ⊆-split (distinct-∉ Hd) H∈ H⊆ =
-- --     tweaken (go Htype) (++⁺ H⊆₁ []) (distinct-weaken Hd)
-- --   ... | no H∉ rewrite subst-fresh u t (∉-dom-fv Htype (¬∈→∉ H∉)) =
-- --     tweaken Htype (⊆-strengthen (¬∈→∉ H∉) H⊆) (distinct-weaken Hd)
-- --   go (tsub Htype H≤ Hsub) = tsub (go Htype) H≤ Hsub
-- --   go {{refl}} (tpromote Htype Hmul) = tpromote (go Htype) (all-weaken Hmul)
