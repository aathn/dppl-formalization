module Properties.Typing (ℝ : Set) where

-- Lemmas purely about typing

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.LocalClosedness
open import Lib.Freshness
open import Lib.FunExt
open import Lib.AbstractionConcretion
open import Lib.BindingSignature

open import Function using (_$_ ; const ; flip)
open import Data.List using (_++_ ; map)
open import Data.List.Properties using (map-++ ; ++-conicalʳ)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.Product using (∃-syntax)

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

mul-lower
  : ∀ {Γ t e c T′ T}
  → Γ ⊢ t :[ e ] T′
  → {{T′ ≡ c ⊙ T}}
  → --------------
    Γ ⊢ t :[ e ] T
mul-lower Htype = {!!}

open LocalClosed
open Body

well-typed-lc
  : ∀ {Γ t e T}
  → Γ ⊢ t :[ e ] T
  → --------------
    lc-at 0 t
well-typed-lc tvar = lc-at-fvar
well-typed-lc (tabs {t = t} Habs) with Иi As Hcof ← Habs = lc-at-op λ
  { ₀ → let Hbody : body (t ₀)
            Hbody = Иi As λ x → lc-at→≻ _ _ $ well-typed-lc (Hcof x)
        in ≻→lc-at _ _ $ body→1≻ _ Hbody
  }
well-typed-lc (tapp Htype Htype₁) = lc-at-op λ
  { ₀ → well-typed-lc Htype
  ; ₁ → well-typed-lc Htype₁
  }
well-typed-lc (tprim _ Htypes) = lc-at-op $ well-typed-lc ∘ Htypes
well-typed-lc treal            = lc-at-op λ()
well-typed-lc (ttup Htypes)    = lc-at-op $ well-typed-lc ∘ Htypes
well-typed-lc (tproj i Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
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
well-typed-lc (tdist _ Htypes) = lc-at-op $ well-typed-lc ∘ Htypes
well-typed-lc (tassume Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tweight Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (texpect Htype)  = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tinfer Htype)   = lc-at-op λ { ₀ → well-typed-lc Htype }
well-typed-lc (tweaken Htype _ _) = well-typed-lc Htype
well-typed-lc (tsub Htype _ _)    = well-typed-lc Htype
well-typed-lc (tpromote Htype _)  = well-typed-lc Htype

dom-∈ : ∀ {Γ x} → x ∈ dom Γ → ∃[ T ] (x , T) ∈ˡ Γ
dom-∈ {x :: Γ} (∈∪₁ ∈[]) = _ , here refl
dom-∈ {x :: Γ} (∈∪₂ x∈Γ) with T , H∈ ← dom-∈ x∈Γ = T , there H∈

∉-dom-fv
  : ∀ {Γ t e T x}
  → Γ ⊢ t :[ e ] T
  → x ∉ dom Γ
  → ---------
    x ∉ fv t
∉-dom-fv = {!!}

open Subst

substitution-pres-typing
  : ∀ {Γ′ Γ x u T₂ t e T₁}
  → Γ , x ∶ T₂ & Γ′ ⊢ t :[ e ] T₁
  → [] ⊢ u :[ det ] T₂
  → -----------------------------
    Γ & Γ′ ⊢ (x => u) t :[ e ] T₁

substitution-pres-typing {Γ′} {Γ} {x} {u} {T₂} Htype Hu = go {{Hu}} Htype
  where
  go
    : ∀ {Γ′ Γ Γ₀ t e T₁ T₂}
    → {{[] ⊢ u :[ det ] T₂}}
    → {{Γ₀ ≡ Γ , x ∶ T₂ & Γ′}}
    → Γ₀ ⊢ t :[ e ] T₁
    → -----------------------------
      Γ & Γ′ ⊢ (x => u) t :[ e ] T₁
  go {{_}} {{Heq}} (tvar {x = x₁})
    with refl , refl , refl ← single-inv {{Heq}}
    rewrite dec-equ x = it
  go {Γ′} {{Hu}} {{refl}} (tabs {t = t} Habs) with Иi As Hcof ← Habs =
    tabs $ Иi ([ x ] ∪ As) λ { y {{∉∪ {{∉x}}}} →
      let Heq : (x => u)((0 ~> y) (t ₀)) ≡ (0 ~> y)((x => u) (t ₀))
          Heq = subst-open-comm (t ₀) (symm≠ y x (∉[]₁ ∉x)) (lc-at→≻ _ _ $ well-typed-lc Hu)
      in
      subst (λ x → _ ⊢ x :[ _ ] _) Heq $ go {Γ′ , y ∶ _} (Hcof y)
    }
  go (tapp Htype Htype₁) = tapp (go Htype) (go Htype₁)
  go (tprim Hϕ Htypes) = tprim Hϕ $ go ∘ Htypes
  go {Γ′} treal with () ← ++-conicalʳ Γ′ _ $ symm it
  go (ttup Htypes) = ttup (go ∘ Htypes)
  go (tproj i Htype) = tproj i $ go Htype
  go (tif Htype Htype₁ Htype₂) =
    tif (go Htype) (go Htype₁) (go Htype₂)
  go (tdiff Hcs Htype Htype₁) =
    tdiff Hcs (go Htype) (go Htype₁)
  go (tsolve Htype Htype₁ Htype₂) =
    tsolve (go Htype) (go Htype₁) (go Htype₂)
  go (tdist HD Htypes) = tdist HD $ go ∘ Htypes
  go (tassume Htype) = tassume $ go Htype
  go (tweight Htype) = tweight $ go Htype
  go (texpect Htype) = texpect $ go Htype
  go (tinfer Htype)  = tinfer  $ go Htype
  go {{_}} {{refl}} (tweaken {Γ = Γ₂} {t = t} Htype H⊆ Hdst) with x ∈? dom Γ₂
  ... | yes H∈ = {!!}
  ... | no  H∉ rewrite subst-fresh u t (∉-dom-fv Htype (¬∈→∉ H∉)) =
    tweaken Htype {!!} {!!}
  go (tsub Htype H≤ Hsub) = tsub (go Htype) H≤ Hsub
  go {Γ′} {{_}} {{refl}} (tpromote Htype Hmul)
    with Γ₁ , Γ₂ , refl , refl , Hmul′ ← map-++-inv {Γ₁ = Γ′} Hmul
    with (x , T′) , Γ₂′ , refl , refl , refl ← map-::-inv Hmul′ =
    tpromote (go {{mul-lower it}} Htype) (symm $ map-++ _ Γ₁ Γ₂′)
