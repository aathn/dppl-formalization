open import Lib.Reals
module Properties.Typing (R : Reals₀) where

-- Lemmas purely about typing

open Reals R hiding (refl)

open import Syntax R
open import Typing R

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets
open import Lib.LocallyNameless.Freshness
open import Lib.LocallyNameless.AbstractionConcretion hiding (abs)
open import Lib.LocallyNameless.BindingSignature
open import Lib.Env
open import Lib.FunExt
open import Lib.Substitution
open import Lib.Util

open import Data.Fin using (fromℕ<)
open import Data.List.Properties using (++-conicalʳ)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_ ; [] ; _∷_ ; _∷ʳ_ ; lookup)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties using (++⁺)
open import Data.List.Relation.Binary.Pointwise as P using ([] ; _∷_)
open import Data.List.Relation.Unary.All as A using ([] ; _∷_)

sub-refl : T <: T
sub-refl {treal c} = sreal ≤refl
sub-refl {T ⇒[ x ] T₁} = sarr sub-refl sub-refl ≤refl
sub-refl {ttup _ ts} = stup (λ i → sub-refl)
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
  → ---------------
  dom Γ₁ ≡ dom Γ₂
sub-dom [] = refl
sub-dom (x≡y ∷ Hsub) = ap₂ _∪_ (ap [_] $ π₁ x≡y) (sub-dom Hsub)

≤ᶜ⇒⊙-noop : c ≤ᶜ T → c ⊙ T ≡ T
≤ᶜ⇒⊙-noop {T = treal c′} H≤ = ap treal {!!}
≤ᶜ⇒⊙-noop {T = _ ⇒[ _ ] _} H≤ = refl
≤ᶜ⇒⊙-noop {T = ttup n Ts} H≤ = ap (ttup n) $ funext λ i → ≤ᶜ⇒⊙-noop (H≤ i)
≤ᶜ⇒⊙-noop {T = tdist _} H≤ = refl

≤ᶜ-<:-trans :
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
  (_ : Γ₁ ⊢ t :[ e ] T)
  (_ : Γ₂ <:ᴱ Γ₁)
  → -------------------
  Γ₂ ⊢ t :[ e ] T
sub-env tvar ((refl , Hsub) ∷ []) = tsub tvar ≤refl Hsub
sub-env (tabs (Иi As Hcof)) Hsub =
  tabs $ Иi As λ y → sub-env (Hcof y) ((refl , sub-refl) ∷ Hsub)
sub-env (tapp Htype Htype₁) Hsub =
  tapp (sub-env Htype Hsub) (sub-env Htype₁ Hsub)
sub-env (tprim Hϕ Hd Htypes) Hsub =
  tprim Hϕ (dom-distinct (symm $ sub-dom Hsub) Hd) λ i → sub-env (Htypes i) Hsub
sub-env treal [] = treal
sub-env (ttup Hd Htypes) Hsub =
  ttup (dom-distinct (symm $ sub-dom Hsub) Hd) λ i → sub-env (Htypes i) Hsub
sub-env (tproj i Htype) Hsub = tproj i (sub-env Htype Hsub)
sub-env (tif Htype Htype₁ Htype₂) Hsub =
  tif (sub-env Htype Hsub) (sub-env Htype₁ Hsub) (sub-env Htype₂ Hsub)
sub-env (tdiff Hc Htype Htype₁) Hsub =
  tdiff Hc (sub-env Htype Hsub) (sub-env Htype₁ Hsub)
sub-env (tsolve Htype Htype₁ Htype₂ H≤) Hsub =
  tsolve (sub-env Htype Hsub) (sub-env Htype₁ Hsub) (sub-env Htype₂ Hsub) H≤
sub-env (tdist HD Hd Htypes) Hsub =
  tdist HD (dom-distinct (symm $ sub-dom Hsub) Hd) λ i → sub-env (Htypes i) Hsub
sub-env (tassume Htype) Hsub = tassume (sub-env Htype Hsub)
sub-env (tweight Htype) Hsub = tweight (sub-env Htype Hsub)
sub-env (tinfer Htype H≤) Hsub  = tinfer (sub-env Htype Hsub) (≤ᴱ-<:ᴱ-trans H≤ Hsub)
sub-env (tweaken Htype H⊆ Hd) Hsub =
  let Γ₂′ , Hsub′ , H⊆′ = sub-⊆ Hsub H⊆
  in  tweaken (sub-env Htype Hsub′) H⊆′ (dom-distinct (symm $ sub-dom Hsub) Hd)
sub-env (tsub Htype H≤ Hsub′) Hsub = tsub (sub-env Htype Hsub) H≤ Hsub′
sub-env (tpromote Htype H≤) Hsub = tpromote (sub-env Htype Hsub) (≤ᴱ-<:ᴱ-trans H≤ Hsub)


tabs-inv :
  {T₀ T₁ T₂ : Type}
  {t : Vector Term 1}
  (_ : Γ ⊢ abs T₀ ▸ t :[ e ] T)
  (_ : T ≡ T₁ ⇒[ e′ ] T₂)
  → --------------------------------------------
  И x ∶ 𝔸 , Γ , x ∶ T₁ ⊢ conc (t ₀) x :[ e′ ] T₂
tabs-inv (tabs Habs) refl = Habs
tabs-inv {Γ} {T₀} (tweaken Htype H⊆ Hd) Heq
  with Иi As Hcof ← tabs-inv Htype Heq =
  Иi (dom Γ ∪ As) λ { x {{∉∪}} → tweaken (Hcof x) (refl ∷ H⊆) (it ∷ Hd) }
tabs-inv (tsub Htype H≤ (sarr Hsub₀ Hsub₁ He)) refl
  with Иi As Hcof ← tabs-inv Htype refl =
  Иi As λ x → sub-env (tsub (Hcof x) He Hsub₁) ((refl , Hsub₀) ∷ P.refl (refl , sub-refl))
tabs-inv (tpromote {T = _ ⇒[ _ ] _} Htype H≤) refl =
  tabs-inv Htype refl

ttup-inv :
  {vs : Vector Term n}
  {Ts : Vector Type n}
  (_ : Γ ⊢ tup n ▸ vs :[ e ] T)
  (_ : T ≡ ttup n Ts)
  → ---------------------------
  ∀ i → Γ ⊢ vs i :[ e ] Ts i
ttup-inv (ttup _ Hvs) refl = Hvs
ttup-inv (tweaken Htype H⊆ Hd) Heq = λ i →
  tweaken (ttup-inv Htype Heq i) H⊆ Hd
ttup-inv (tsub Htype H≤ (stup Hsubs)) refl = λ i →
  tsub (ttup-inv Htype refl i) H≤ (Hsubs i)
ttup-inv (tpromote {T = ttup _ _} Htype H≤) refl = λ i →
  tpromote (ttup-inv Htype refl i) H≤

tassume-inv :
  {rs : Vector ℝ (DistAr D)}
  → Γ ⊢ dist D ▸ (real ∘ rs) :[ e ] T
  → T ≡ tdist T′
  → -------------------------------------------------
    ∃ λ cs → ∃ λ T″ → DistTy D ≡ (cs , T″) × T″ <: T′
tassume-inv (tdist HD _ _) refl = _ , _ , HD , sub-refl
tassume-inv (tweaken Htype H⊆ Hd) Heq =
  tassume-inv Htype Heq
tassume-inv (tsub Htype H≤ (sdist Hsub)) refl with tassume-inv Htype refl
... | cs , T , Heq , Hsub′ = cs , T , Heq , sub-trans Hsub′ Hsub
tassume-inv (tpromote {T = tdist _} Htype H≤) refl =
  tassume-inv Htype refl

tinfer-inv :
  {v : Vector Term 1}
  (_ : Γ ⊢ infer ▸ v :[ e ] T)
  → T ≡ tdist T′
  → --------------------------------
    Γ ⊢ v ₀ :[ e ] tunit ⇒[ rnd ] T′
tinfer-inv (tinfer Htype _) refl = Htype
tinfer-inv (tweaken Htype H⊆ Hd) Heq =
  tweaken (tinfer-inv Htype Heq) H⊆ Hd
tinfer-inv (tsub Htype H≤ (sdist Hsub)) refl =
  tsub (tinfer-inv Htype refl) H≤ (sarr sub-refl Hsub ≤refl)
tinfer-inv (tpromote {T = tdist _} Htype H≤) refl =
  tpromote (tinfer-inv Htype refl) H≤


well-typed-distinct : Γ ⊢ t :[ e ] T → Distinct Γ

well-typed-distinct tvar = ∉Ø ∷ []
well-typed-distinct (tabs (Иi As Hcof))
  with x , x∉As ← fresh As
  with _ ∷ Hd ← well-typed-distinct (Hcof x {{x∉As}}) = Hd
well-typed-distinct (tapp Htype Htype₁) = well-typed-distinct Htype
well-typed-distinct (tprim Hϕ Hd _) = Hd
well-typed-distinct treal = []
well-typed-distinct (ttup Hd _) = Hd
well-typed-distinct (tproj i Htype) = well-typed-distinct Htype
well-typed-distinct (tif Htype Htype₁ Htype₂) = well-typed-distinct Htype
well-typed-distinct (tdiff _ Htype Htype₁) = well-typed-distinct Htype
well-typed-distinct (tsolve Htype Htype₁ Htype₂ _) = well-typed-distinct Htype
well-typed-distinct (tdist HD Hd _) = Hd
well-typed-distinct (tassume Htype) = well-typed-distinct Htype
well-typed-distinct (tweight Htype) = well-typed-distinct Htype
well-typed-distinct (tinfer Htype _)  = well-typed-distinct Htype
well-typed-distinct (tweaken _ _ Hd) = Hd
well-typed-distinct (tsub Htype _ _) = well-typed-distinct Htype
well-typed-distinct (tpromote Htype _) = well-typed-distinct Htype


∉-dom-fv :
  {x : 𝔸}
  (_ : Γ ⊢ t :[ e ] T)
  (_ : x ∉ dom Γ)
  → ------------------
  x ∉ fv t
∉-dom-fv tvar (∉∪ {{p}}) = p
∉-dom-fv {x = x} (tabs {t = t} (Иi As Hcof)) H∉
  with y , ∉∪ {{∉[]}} ← fresh {𝔸} ([ x ] ∪ As)
  with Hnin ← ∉-dom-fv {x = x} (Hcof y) (∉∪ {{p = ∉[] {{p = symm≠ y x it}}}} {{H∉}}) =
  ∉∪ {{p = open-notin (t ₀) Hnin}}
∉-dom-fv (tapp Htype Htype₁) H∉ =
  ∉∪ {{p = ∉-dom-fv Htype H∉}} {{∉∪ {{p = ∉-dom-fv Htype₁ H∉}}}}
∉-dom-fv (tprim _ _ Htypes) H∉ = ∉⋃′ _ λ i → ∉-dom-fv (Htypes i) H∉
∉-dom-fv treal H∉ = ∉Ø
∉-dom-fv (ttup _ Htypes) H∉ = ∉⋃′ _ λ i → ∉-dom-fv (Htypes i) H∉
∉-dom-fv (tproj i Htype) H∉ = ∉∪ {{p = ∉-dom-fv Htype H∉}}
∉-dom-fv (tif Htype Htype₁ Htype₂) H∉ =
  ∉∪ {{p = ∉-dom-fv Htype H∉}}
    {{∉∪ {{p = ∉-dom-fv Htype₁ H∉}}
      {{∉∪ {{p = ∉-dom-fv Htype₂ H∉}} }} }}
∉-dom-fv (tdiff _ Htype Htype₁) H∉ =
  ∉∪ {{p = ∉-dom-fv Htype H∉}} {{∉∪ {{p = ∉-dom-fv Htype₁ H∉}}}}
∉-dom-fv (tsolve Htype Htype₁ Htype₂ _) H∉ =
  ∉∪ {{p = ∉-dom-fv Htype H∉}}
    {{∉∪ {{p = ∉-dom-fv Htype₁ H∉}}
      {{∉∪ {{p = ∉-dom-fv Htype₂ H∉}} }} }}
∉-dom-fv (tdist _ _ Htypes) H∉ = ∉⋃′ _ λ i → ∉-dom-fv (Htypes i) H∉
∉-dom-fv (tassume Htype) H∉ = ∉∪ {{p = ∉-dom-fv Htype H∉}}
∉-dom-fv (tweight Htype) H∉ = ∉∪ {{p = ∉-dom-fv Htype H∉}}
∉-dom-fv (tinfer Htype _) H∉  = ∉∪ {{p = ∉-dom-fv Htype H∉}}
∉-dom-fv (tweaken Htype H⊆ _) H∉ = ∉-dom-fv Htype (∉-dom-⊆ H⊆ H∉)
∉-dom-fv (tsub Htype _ _) H∉ = ∉-dom-fv Htype H∉
∉-dom-fv (tpromote Htype _) H∉ = ∉-dom-fv Htype H∉

open LocalClosed
open Body

well-typed-lc : Γ ⊢ t :[ e ] T → lc-at 0 t

well-typed-lc tvar = lc-at-fvar
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
well-typed-lc treal              = lc-at-op λ()
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
well-typed-lc (tsolve Htype Htype₁ Htype₂ _) = lc-at-op λ
  { ₀ → well-typed-lc Htype
  ; ₁ → well-typed-lc Htype₁
  ; ₂ → well-typed-lc Htype₂
  }
well-typed-lc (tdist _ _ Htypes) = lc-at-op $ well-typed-lc ∘ Htypes
well-typed-lc (tassume Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tweight Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tinfer Htype _)   = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tweaken Htype _ _) = well-typed-lc Htype
well-typed-lc (tsub Htype _ _)    = well-typed-lc Htype
well-typed-lc (tpromote Htype _)  = well-typed-lc Htype

substitution-pres-typing :
  {x : 𝔸}
  {t u : Term}
  {T₁ T₂ : Type}
  (_ : [ x ∶ T₂ ] & Γ′ ⊢ t :[ e ] T₁)
  (_ : [] ⊢ u :[ det ] T₂)
  → ---------------------------------
  [] & Γ′ ⊢ (x => u) t :[ e ] T₁
substitution-pres-typing {Γ′ = Γ′} {x = x} {u = u} {T₂ = T₂} Htype Hu = go Htype
  where
  go :
    {Γ′ Γ₀ : TyEnv}
    {T₁ : Type}
    {{_ : Γ₀ ≡ [ x ∶ T₂ ] & Γ′}}
    (_ : Γ₀ ⊢ t :[ e ] T₁)
    → ----------------------------
    [] & Γ′ ⊢ (x => u) t :[ e ] T₁
  go {{Heq}} (tvar {x = x₁})
    with refl , refl , refl ← single-inv {{Heq}}
    rewrite dec-equ x = Hu
  go {Γ′ = Γ′} {{refl}} (tabs {t = t} (Иi As Hcof)) =
    tabs $ Иi ([ x ] ∪ As) λ { y {{∉∪ {{∉x}}}} →
      let Heq : (x => u)((0 ~> y) (t ₀)) ≡ (0 ~> y)((x => u) (t ₀))
          Heq = subst-open-comm (t ₀) (symm≠ y x (∉[]₁ ∉x)) (lc-at→≻ _ _ $ well-typed-lc Hu)
      in
      subst (λ x → _ ⊢ x :[ _ ] _) Heq $ go {Γ′ = Γ′ , y ∶ _} (Hcof y)
    }
  go (tapp Htype Htype₁) = tapp (go Htype) (go Htype₁)
  go {{refl}} (tprim Hϕ Hd Htypes) = tprim Hϕ (distinct-weaken Hd) (go ∘ Htypes)
  go {Γ′ = Γ′} treal with () ← ++-conicalʳ Γ′ _ $ symm it
  go {{refl}} (ttup Hd Htypes) = ttup (distinct-weaken Hd) (go ∘ Htypes)
  go (tproj i Htype) = tproj i $ go Htype
  go (tif Htype Htype₁ Htype₂) =
    tif (go Htype) (go Htype₁) (go Htype₂)
  go (tdiff Hcs Htype Htype₁) =
    tdiff Hcs (go Htype) (go Htype₁)
  go (tsolve Htype Htype₁ Htype₂ H≤) =
    tsolve (go Htype) (go Htype₁) (go Htype₂) H≤
  go {{refl}} (tdist HD Hd Htypes) = tdist HD (distinct-weaken Hd) (go ∘ Htypes)
  go (tassume Htype) = tassume $ go Htype
  go (tweight Htype) = tweight $ go Htype
  go {{refl}} (tinfer Htype H≤) = tinfer (go Htype) (all-weaken insert-⊆ H≤)
  go {{refl}} (tweaken {Γ′ = Γ₂} {t = t} Htype H⊆ Hd) with x ∈? dom Γ₂
  ... | yes H∈ with Δ₁ , Δ₂ , [] , H⊆₁ , refl ← ⊆-split (distinct-∉ Hd) H∈ H⊆ =
    tweaken (go Htype) (++⁺ H⊆₁ []) (distinct-weaken Hd)
  ... | no H∉ rewrite subst-fresh u t (∉-dom-fv Htype (¬∈→∉ H∉)) =
    tweaken Htype (⊆-strengthen (¬∈→∉ H∉) H⊆) (distinct-weaken Hd)
  go (tsub Htype H≤ Hsub) = tsub (go Htype) H≤ Hsub
  go {{refl}} (tpromote Htype Hmul) = tpromote (go Htype) (all-weaken insert-⊆ Hmul)
