module Properties.Typing (ℝ : Set) where

-- Lemmas purely about typing

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.LocalClosedness
open import Lib.Freshness
open import Lib.FunExt
open import Lib.AbstractionConcretion hiding (abs)
open import Lib.BindingSignature

open import Function using (_$_ ; const ; flip)
open import Data.List using (_++_ ; map)
open import Data.List.Properties using (map-++ ; ++-conicalʳ)
open import Data.List.Relation.Binary.Sublist.Propositional using ([] ; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise ; [] ; _∷_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([] ; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.Nat.Properties using (m≤n⇒m⊔n≡n)
open import Data.Product using (∃-syntax)
import Relation.Binary.PropositionalEquality as ≡

open import Syntax ℝ
open import Typing ℝ
open import Properties.Util

infixl 5 _&_
_&_ : TyEnv → TyEnv → TyEnv
_&_ = flip _++_

sub-refl : ∀ {T} → T <: T
sub-refl {treal c} = sreal ≤refl
sub-refl {T ⇒[ x ] T₁} = sarr sub-refl sub-refl ≤refl
sub-refl {ttup ts} = stup (λ i → sub-refl)
sub-refl {tdist T} = sdist sub-refl

sub-trans : ∀ {T₁ T₂ T₃} → T₁ <: T₂ → T₂ <: T₃ → T₁ <: T₃
sub-trans (sreal H≤) (sreal H≤′) = sreal (≤trans H≤′ H≤)
sub-trans (stup Hsubs) (stup Hsubs′) = stup (λ i → sub-trans (Hsubs i) (Hsubs′ i))
sub-trans (sarr Hsub1 Hsub4 H≤) (sarr Hsub2 Hsub3 H≤′) =
  sarr (sub-trans Hsub2 Hsub1) (sub-trans Hsub4 Hsub3) (≤trans H≤ H≤′)
sub-trans (sdist Hsub1) (sdist Hsub2) = sdist (sub-trans Hsub1 Hsub2)

sub-mul
  : ∀ {T c}
  → ----------
    c ⊙ T <: T
sub-mul {treal x} = sreal ≤max₂
sub-mul {T ⇒[ x ] T₁} = sub-refl
sub-mul {ttup ts} = stup (λ i → sub-mul)
sub-mul {tdist T} = sub-refl

mul-idempotent
  : ∀ {T c}
  → --------------------
    c ⊙ (c ⊙ T) ≡ c ⊙ T
mul-idempotent {treal x} {c} rewrite m≤n⇒m⊔n≡n {c} {max c x} ≤max₁ = refl
mul-idempotent {T ⇒[ e ] T₁} = refl
mul-idempotent {ttup Ts} = ap ttup $ funext λ i → mul-idempotent {Ts i}
mul-idempotent {tdist T} = refl

well-typed-distinct
  : ∀ {Γ t e T}
  → Γ ⊢ t :[ e ] T
  → --------------
    Distinct Γ

well-typed-distinct tvar = [] ∷ []
well-typed-distinct (tabs (Иi As Hcof))
  with x , x∉As ← fresh As
  with _ ∷ Hd ← well-typed-distinct (Hcof x {{x∉As}}) = Hd
well-typed-distinct (tapp Htype Htype₁) = well-typed-distinct Htype
well-typed-distinct (tprim Hϕ Htypes Hd) = Hd
well-typed-distinct treal = []
well-typed-distinct (ttup Htypes Hd) = Hd
well-typed-distinct (tproj i Htype) = well-typed-distinct Htype
well-typed-distinct (tif Htype Htype₁ Htype₂) = well-typed-distinct Htype
well-typed-distinct (tdiff _ Htype Htype₁) = well-typed-distinct Htype
well-typed-distinct (tsolve Htype Htype₁ Htype₂) = well-typed-distinct Htype
well-typed-distinct (tdist HD Htypes Hd) = Hd
well-typed-distinct (tassume Htype) = well-typed-distinct Htype
well-typed-distinct (tweight Htype) = well-typed-distinct Htype
well-typed-distinct (texpect Htype) = well-typed-distinct Htype
well-typed-distinct (tinfer Htype)  = well-typed-distinct Htype
well-typed-distinct (tweaken _ _ Hd) = Hd
well-typed-distinct (tsub Htype _ _) = well-typed-distinct Htype
well-typed-distinct (tpromote Htype _) = well-typed-distinct Htype

∉-dom-distinct
  : ∀ {Γ x T}
  → x ∉ dom Γ
  → ----------------------------
    All (DistinctName (x , T)) Γ
∉-dom-distinct {[]} ∉Ø = []
∉-dom-distinct {(y , T′) :: Γ} {T = T} (∉∪ {{∉[]}}) =
  ≠→¬≡ it ∷ ∉-dom-distinct {T = T} it

sub-var
  : ∀ {Γ₀ Γ₁ Γ₂ Γ t e T}
  → Γ₀ ⊢ t :[ e ] T
  → Γ₀ ≡ Γ & Γ₂
  → Pointwise (λ x y → π₂ x <: π₂ y) Γ₁ Γ₂
  → --------------------------------------
    Γ & Γ₁ ⊢ t :[ e ] T
sub-var Htype Heq Hpt = {!!}

tabs-inv :
  ∀ {Γ T₀ t e T e′ T₁ T₂}
  → Γ ⊢ abs T₀ t :[ e ] T
  → T ≡ T₁ ⇒[ e′ ] T₂
  → ----------------------------------------------
    И x ∶ 𝔸 , Γ , x ∶ T₁ ⊢ conc (t ₀) x :[ e′ ] T₂
tabs-inv (tabs Habs) refl = Habs
tabs-inv {Γ} {T₀} (tweaken Htype H⊆ Hd) Heq
  with Иi As Hcof ← tabs-inv Htype Heq =
 Иi (dom Γ ∪ As) λ { x {{∉∪}} →
    tweaken (Hcof x) (refl ∷ H⊆) (∉-dom-distinct {T = T₀} it ∷ Hd)
  }
tabs-inv (tsub Htype H≤ (sarr Hsub₀ Hsub₁ He)) refl
  with Иi As Hcof ← tabs-inv Htype refl =
  Иi As λ x → sub-var (tsub (Hcof x) He Hsub₁) refl (Hsub₀ ∷ [])
tabs-inv (tpromote {T = _ ⇒[ _ ] _} Htype H≤) refl =
  tabs-inv Htype refl

ttup-inv :
  ∀ {n Γ vs e T Ts}
  → Γ ⊢ tup {n} vs :[ e ] T
  → T ≡ ttup Ts
  → --------------------------
    ∀ i → Γ ⊢ vs i :[ e ] Ts i
ttup-inv (ttup Hvs _) refl = Hvs
ttup-inv (tweaken Htype H⊆ Hd) Heq = λ i →
  tweaken (ttup-inv Htype Heq i) H⊆ Hd
ttup-inv (tsub Htype H≤ (stup Hsubs)) refl = λ i →
  tsub (ttup-inv Htype refl i) H≤ (Hsubs i)
ttup-inv (tpromote {T = ttup _} Htype H≤) refl = λ i →
  tpromote (ttup-inv Htype refl i) H≤

texpect-inv :
  ∀ {Γ D rs e T T′}
  → Γ ⊢ dist D (real ∘ rs) :[ e ] T
  → T ≡ tdist T′
  → -----------------------------------------------
    ∃[ cs ] ∃[ T″ ] DistTy D ≡ (cs , T″) × T″ <: T′
texpect-inv (tdist HD _ _) refl = _ , _ , HD , sub-refl
texpect-inv (tweaken Htype H⊆ Hd) Heq =
  texpect-inv Htype Heq
texpect-inv (tsub Htype H≤ (sdist Hsub)) refl with texpect-inv Htype refl
... | cs , T , Heq , Hsub′ = cs , T , Heq , sub-trans Hsub′ Hsub
texpect-inv (tpromote {T = tdist _} Htype H≤) refl =
  texpect-inv Htype refl

tinfer-inv :
  ∀ {Γ v e T T′}
  → Γ ⊢ infer v :[ e ] T
  → T ≡ tdist T′
  → --------------------------------
    Γ ⊢ v ₀ :[ e ] tunit ⇒[ rnd ] T′
tinfer-inv (tinfer Htype) refl = Htype
tinfer-inv (tweaken Htype H⊆ Hd) Heq =
  tweaken (tinfer-inv Htype Heq) H⊆ Hd
tinfer-inv (tsub Htype H≤ (sdist Hsub)) refl =
  tsub (tinfer-inv Htype refl) H≤ (sarr sub-refl Hsub ≤refl)
tinfer-inv (tpromote {T = tdist _} Htype H≤) refl =
  tpromote (tinfer-inv Htype refl) H≤

-- dom-∈ : ∀ {Γ x} → x ∈ dom Γ → ∃[ T ] (x , T) ∈ˡ Γ
-- dom-∈ {x :: Γ} (∈∪₁ ∈[]) = _ , here refl
-- dom-∈ {x :: Γ} (∈∪₂ x∈Γ) with T , H∈ ← dom-∈ x∈Γ = T , there H∈

∉-dom-fv
  : ∀ {x Γ t e T}
  → Γ ⊢ t :[ e ] T
  → x ∉ dom Γ
  → ---------
    x ∉ fv t
∉-dom-fv tvar (∉∪ {{p}}) = p
∉-dom-fv {x} (tabs {t = t} (Иi As Hcof)) H∉
  with y , ∉∪ {{∉[]}} ← fresh {𝔸} ([ x ] ∪ As)
  with Hnin ← ∉-dom-fv {x} (Hcof y) (∉∪ {{p = ∉[] {{p = symm≠ y x it}}}} {{H∉}}) =
  ∉∪ {{p = open-notin (t ₀) Hnin}}
∉-dom-fv (tapp Htype Htype₁) H∉ =
  ∉∪ {{p = ∉-dom-fv Htype H∉}} {{∉∪ {{p = ∉-dom-fv Htype₁ H∉}}}}
∉-dom-fv (tprim x x₁ x₂) H∉ = {!!}
∉-dom-fv treal H∉ = {!!}
∉-dom-fv (ttup x x₁) H∉ = {!!}
∉-dom-fv (tproj i Htype) H∉ = {!!}
∉-dom-fv (tif Htype Htype₁ Htype₂) H∉ = {!!}
∉-dom-fv (tdiff x Htype Htype₁) H∉ = {!!}
∉-dom-fv (tsolve Htype Htype₁ Htype₂) H∉ = {!!}
∉-dom-fv (tdist x x₁ x₂) H∉ = {!!}
∉-dom-fv (tassume Htype) H∉ = {!!}
∉-dom-fv (tweight Htype) H∉ = {!!}
∉-dom-fv (texpect Htype) H∉ = {!!}
∉-dom-fv (tinfer Htype) H∉ = {!!}
∉-dom-fv (tweaken Htype x x₁) H∉ = {!!}
∉-dom-fv (tsub Htype x x₁) H∉ = {!!}
∉-dom-fv (tpromote Htype x) H∉ = {!!}

all-weaken
  : ∀ {A : Set} {P : A → Set} {l₁ l₂ x}
  → All P (l₁ ++ x :: l₂)
  → ---------------------
    All P (l₁ ++ l₂)
all-weaken {l₁ = []} (px ∷ Hall) = Hall
all-weaken {l₁ = x :: l₁} (px ∷ Hall) = px ∷ all-weaken Hall

distinct-weaken
  : ∀ {Γ′ Γ x T}
  → Distinct (Γ , x ∶ T & Γ′)
  → -------------------------
    Distinct (Γ & Γ′)
distinct-weaken {[]} (x ∷ Hd) = Hd
distinct-weaken {x :: Γ′} (x₁ ∷ Hd) = all-weaken x₁ ∷ distinct-weaken Hd


open LocalClosed
open Body

well-typed-lc
  : ∀ {Γ t e T}
  → Γ ⊢ t :[ e ] T
  → --------------
    lc-at 0 t
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
well-typed-lc (tprim _ Htypes _) = lc-at-op $ well-typed-lc ∘ Htypes
well-typed-lc treal              = lc-at-op λ()
well-typed-lc (ttup Htypes _)    = lc-at-op $ well-typed-lc ∘ Htypes
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
well-typed-lc (tdist _ Htypes _) = lc-at-op $ well-typed-lc ∘ Htypes
well-typed-lc (tassume Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tweight Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (texpect Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tinfer Htype)   = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tweaken Htype _ _) = well-typed-lc Htype
well-typed-lc (tsub Htype _ _)    = well-typed-lc Htype
well-typed-lc (tpromote Htype _)  = well-typed-lc Htype

open Subst

substitution-pres-typing
  : ∀ {Γ′ Γ x u T₂ t e T₁}
  → Γ , x ∶ T₂ & Γ′ ⊢ t :[ e ] T₁
  → Γ ⊢ u :[ det ] T₂
  → -----------------------------
    Γ & Γ′ ⊢ (x => u) t :[ e ] T₁
substitution-pres-typing {Γ′} {Γ} {x} {u} {T₂} Htype Hu = go {{refl}} {{Hu}} Htype
  where
  go
    : ∀ {Γ′ Γ Γ₀ t e T₁ T₂}
    → {{Γ₀ ≡ Γ , x ∶ T₂ & Γ′}}
    → {{Γ ⊢ u :[ det ] T₂}}
    → Γ₀ ⊢ t :[ e ] T₁
    → -----------------------------
      Γ & Γ′ ⊢ (x => u) t :[ e ] T₁
  go {{Heq}} (tvar {x = x₁})
    with refl , refl , refl ← single-inv {{Heq}}
    rewrite dec-equ x = it
  go {Γ′} {{refl}} {{Hu}} (tabs {t = t} (Иi As Hcof)) =
    tabs $ Иi ([ x ] ∪ As) λ { y {{∉∪ {{∉x}}}} →
      let Heq : (x => u)((0 ~> y) (t ₀)) ≡ (0 ~> y)((x => u) (t ₀))
          Heq = subst-open-comm (t ₀) (symm≠ y x (∉[]₁ ∉x)) (lc-at→≻ _ _ $ well-typed-lc Hu)
      in
      subst (λ x → _ ⊢ x :[ _ ] _) Heq $ go {Γ′ , y ∶ _} (Hcof y)
    }
  go (tapp Htype Htype₁) = tapp (go Htype) (go Htype₁)
  go {{refl}} (tprim Hϕ Htypes Hd) = tprim Hϕ (go ∘ Htypes) (distinct-weaken Hd)
  go {Γ′} treal with () ← ++-conicalʳ Γ′ _ $ symm it
  go {{refl}} (ttup Htypes Hd) = ttup (go ∘ Htypes) (distinct-weaken Hd)
  go (tproj i Htype) = tproj i $ go Htype
  go (tif Htype Htype₁ Htype₂) =
    tif (go Htype) (go Htype₁) (go Htype₂)
  go (tdiff Hcs Htype Htype₁) =
    tdiff Hcs (go Htype) (go Htype₁)
  go (tsolve Htype Htype₁ Htype₂) =
    tsolve (go Htype) (go Htype₁) (go Htype₂)
  go {{refl}} (tdist HD Htypes Hd) = tdist HD (go ∘ Htypes) (distinct-weaken Hd)
  go (tassume Htype) = tassume $ go Htype
  go (tweight Htype) = tweight $ go Htype
  go (texpect Htype) = texpect $ go Htype
  go (tinfer Htype)  = tinfer  $ go Htype
  go {{refl}} (tweaken {Γ = Γ₂} {t = t} Htype H⊆ Hd) with x ∈? dom Γ₂
  ... | yes H∈ = {!!}
  ... | no  H∉ = {!!} -- rewrite subst-fresh u t (∉-dom-fv Htype (¬∈→∉ H∉)) =
    -- tweaken Htype {!!} {!!}
  go (tsub Htype H≤ Hsub) = tsub (go Htype) H≤ Hsub
  go {{refl}} (tpromote Htype Hmul) = tpromote (go Htype) (all-weaken Hmul)
