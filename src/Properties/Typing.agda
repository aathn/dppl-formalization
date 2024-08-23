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
open import Lib.AbstractionConcretion
open import Lib.BindingSignature
open import Lib.Substitution

open import Data.Fin using (toℕ ; fromℕ< ; _≤?_)
open import Data.Fin.Properties using (toℕ<n ; toℕ-fromℕ< ; fromℕ<-toℕ)
open import Data.List using (_++_)
open import Data.List.Relation.Binary.Sublist.Propositional
  using (_⊆_ ; [] ; _∷_ ; _∷ʳ_ ; ⊆-refl ; ⊆-trans ; from∈ ; to∈)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties as SP using ()
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Relation.Unary.Any.Properties as AnyP using ()
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴱ_)
open import Data.List.Membership.Propositional.Properties as MP using ()

infixl 5 _&_
_&_ : TyEnv → TyEnv → TyEnv
Γ & Γ′ = Γ′ ++ Γ

sub-refl : {T : Type} → T <: T
sub-refl {treal c} = sreal ≤refl
sub-refl {T ⇒[ x ] T₁} = sarr sub-refl ≤refl sub-refl
sub-refl {ttup ts} = stup (λ i → sub-refl)
sub-refl {tdist T} = sdist sub-refl

sub-trans : {T₁ T₂ T₃ : Type} → T₁ <: T₂ → T₂ <: T₃ → T₁ <: T₃
sub-trans (sreal H≤) (sreal H≤′) = sreal (≤trans H≤′ H≤)
sub-trans (stup Hsubs) (stup Hsubs′) = stup (λ i → sub-trans (Hsubs i) (Hsubs′ i))
sub-trans (sarr Hsub1 H≤ Hsub4) (sarr Hsub2 H≤′ Hsub3) =
  sarr (sub-trans Hsub2 Hsub1) (≤trans H≤ H≤′) (sub-trans Hsub4 Hsub3)
sub-trans (sdist Hsub1) (sdist Hsub2) = sdist (sub-trans Hsub1 Hsub2)

sub-mul : {T : Type}{c : Coeff} → c ⊙ T <: T
sub-mul {treal x} = sreal $ subst (_ ≤_) (symm $ toℕ-fromℕ< _) ≤max₂
sub-mul {T ⇒[ x ] T₁} = sub-refl
sub-mul {ttup ts} = stup (λ i → sub-mul)
sub-mul {tdist T} = sub-refl

mul-≤ : {T : Type}{c : Coeff} → c ≤ᶜ T → T ≡ c ⊙ T
mul-≤ {treal c′} H≤ = ap treal $ symm $ m≤′n⇒m⊔′n≡n H≤
mul-≤ {ttup Ts} H≤  = ap ttup $ funext $ mul-≤ ∘ H≤
mul-≤ {_ ⇒[ _ ] _} H≤ = refl
mul-≤ {tdist _} H≤ = refl

weaken-typing :
  {Γ Γ′ : TyEnv}
  {c : Coeff}
  {t : Term}
  {e : Eff}
  {T : Type}
  (_ : Γ′ ⊢[ c ] t :[ e ] T)
  (_ : Γ′ ⊆ Γ)
  (_ : Distinct Γ)
  → -------------------
  Γ ⊢[ c ] t :[ e ] T
weaken-typing (tvar H∈ H≤ _) H⊆ Hd = tvar (to∈ (⊆-trans (from∈ H∈) H⊆)) H≤ Hd
weaken-typing {Γ} (tlam (Иi As Htype)) H⊆ Hd =
  tlam $ Иi (dom Γ ∪ As) λ
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
weaken-typing (tsub Htype H≤₁ H≤₂) H⊆ Hd = tsub (weaken-typing Htype H⊆ Hd) H≤₁ H≤₂
weaken-typing (tpromote Htype H≤) H⊆ Hd = tpromote (weaken-typing Htype H⊆ Hd) H≤
weaken-typing (tdemote Htype H≤) H⊆ Hd = tdemote (weaken-typing Htype H⊆ Hd) H≤

weaken-coeff :
  {Γ : TyEnv}
  {c c′ : Coeff}
  {t : Term}
  {e : Eff}
  {T : Type}
  (_ : Γ ⊢[ c ] t :[ e ] T)
  (_ : c′ ≤′ c)
  → -----------------------
  Γ ⊢[ c′ ] t :[ e ] T
weaken-coeff {c = c} Htype H≤ =
  tsub (tpromote Htype (symm $ m≤′n⇒m⊔′n≡n H≤)) ≤refl sub-mul


-- tlam-inv :
--   ∀ {Γ c T₀ t e T e′ T₁ T₂}
--   → Γ ⊢[ c ] lam T₀ t :[ e ] T
--   → T ≡ T₁ ⇒[ e′ ] T₂
--   → ---------------------------------------------------
--     И x ∶ 𝔸 , Γ , x ∶ T₁ ⊢[ A ] conc (t ₀) x :[ e′ ] T₂
-- tlam-inv (tlam Hlam) refl = {!!} -- Hlam
-- tlam-inv (tsub Htype H≤ (sarr Hsub₀ He Hsub₁)) refl = {!!}
--   -- with Иi As Hcof ← tlam-inv Htype refl =
--   -- Иi As λ x → sub-env (tsub (Hcof x) He Hsub₁) ((refl , Hsub₀) ∷ P.refl (refl , sub-refl))
-- tlam-inv (tpromote {Γ} {T = _ ⇒[ _ ] _} Htype H≤) refl = {!!}
--   -- with Иi As Hcof ← tlam-inv Htype refl =
--   -- Иi (dom Γ ∪ As) λ { x {{∉∪}} → weaken-coeff (Hcof x) {!!} }
-- tlam-inv (tdemote {Γ} {T = _ ⇒[ _ ] _} Htype H≤) refl = {!!}
--   -- with Иi As Hcof ← tlam-inv Htype refl =
--   -- Иi (dom Γ ∪ As) λ { x {{∉∪}} → let foo = Hcof x in {!!} }

ttup-inv :
  {n : ℕ}
  {Γ : TyEnv}
  {c : Coeff}
  {vs : Vector Term n}
  {e : Eff}
  {T : Type}
  {Ts : Vector Type n}
  (_ : Γ ⊢[ c ] tup vs :[ e ] T)
  (_ : T ≡ ttup Ts)
  → -----------------------------
  ∀ i → Γ ⊢[ c ] vs i :[ e ] Ts i
ttup-inv (ttup _ Hvs) refl = Hvs
ttup-inv (tsub Htype H≤ (stup Hsubs)) refl = λ i →
  tsub (ttup-inv Htype refl i) H≤ (Hsubs i)
ttup-inv (tpromote {T = ttup _} Htype H≤) refl = λ i →
  tpromote (ttup-inv Htype refl i) H≤
ttup-inv (tdemote {T = ttup _} Htype H≤) refl = λ i →
  tdemote (ttup-inv Htype refl i) H≤

-- texpect-inv :
--   {Γ : TyEnv}
--   {D : Dist}
--   {rs : Vector ℝ (DistAr D)}
--   {e : Eff}
--   {T T′ : Type}
--   (_ : Γ ⊢ dist D (real ∘ rs) :[ e ] T)
--   (_ : T ≡ tdist T′)
--   → -----------------------------------------------
--   ∃ λ cs → ∃ λ T″ → DistTy D ≡ (cs , T″) × T″ <: T′
-- texpect-inv (tdist HD _ _) refl = _ , _ , HD , sub-refl
-- texpect-inv (tsub Htype H≤ (sdist Hsub)) refl with texpect-inv Htype refl
-- ... | _ , _ , Heq , Hsub′ = _ , _ , Heq , sub-trans Hsub′ Hsub
-- texpect-inv (tpromote {T = tdist _} Htype H≤ H⊆ Hd) refl =
--   texpect-inv Htype refl

-- tinfer-inv :
--   {Γ : TyEnv}
--   {v : Vector Term 1}
--   {e : Eff}
--   {T T′ : Type}
--   (_ : Γ ⊢ infer v :[ e ] T)
--   (_ : T ≡ tdist T′)
--   → ------------------------------
--   Γ ⊢ v ₀ :[ e ] tunit ⇒[ rnd ] T′
-- tinfer-inv (tinfer Htype) refl = Htype
-- tinfer-inv (tsub Htype H≤ (sdist Hsub)) refl =
--   tsub (tinfer-inv Htype refl) H≤ (sarr sub-refl Hsub ≤refl)
-- tinfer-inv (tpromote {T = tdist _} Htype H≤ H⊆ Hd) refl =
--   tpromote (tinfer-inv Htype refl) H≤ H⊆ Hd

-- dom-∈ : {Γ : TyEnv}{x : 𝔸} → x ∈ dom Γ → ∃ λ T → (x , T) ∈ᴱ Γ
-- dom-∈ {x ∷ Γ} (∈∪₁ ∈[]) = _ , here refl
-- dom-∈ {x ∷ Γ} (∈∪₂ x∈Γ) with T , H∈ ← dom-∈ x∈Γ = T , there H∈

∈-dom : {Γ : TyEnv}{x : 𝔸}{T : Type} → (x , T) ∈ᴱ Γ → x ∈ dom Γ
∈-dom {x ∷ Γ} (here refl) = ∈∪₁ ∈[]
∈-dom {x ∷ Γ} (there H∈)  = ∈∪₂ (∈-dom H∈)

&-dom : {Γ : TyEnv}{x : 𝔸}(Γ′ : TyEnv) → x ∉ dom (Γ & Γ′) → x ∉ dom Γ′ ∪ dom Γ
&-dom [] H∉ = ∉∪ {{q = H∉}}
&-dom ((y , T) ∷ Γ′) (∉∪ {{p = H∉₁}} {{H∉₂}}) with ∉∪ ← &-dom Γ′ H∉₂ =
  ∉∪ {{p = ∉∪ {{p = H∉₁}}}}

dom-& : {Γ′ Γ : TyEnv} {x : 𝔸} → x ∉ dom Γ′ ∪ dom Γ → x ∉ dom (Γ & Γ′)
dom-& {[]} ∉∪ = it
dom-& {_ ∷ Γ′} {Γ} {x} (∉∪ {{∉∪ {{p = H∉}}}}) = ∉∪ {{p = H∉}} {{dom-& it}}

weaken-distinct :
  {Γ′ Γ : TyEnv}
  {x : 𝔸}
  {T : Type}
  → -------------------------------------------
  Distinct (Γ , x ∶ T & Γ′) → Distinct (Γ & Γ′)
weaken-distinct {[]} (x ∷ Hd) = Hd
weaken-distinct {Γ′ , x′ ∶ T′} {Γ} {x} {T} (H∉ ∷ Hd)
  with ∉∪ {{q = ∉∪}} ← &-dom Γ′ H∉ =
  dom-& it ∷ weaken-distinct Hd

well-typed-distinct :
  {Γ : TyEnv}
  {c : Coeff}
  {t : Term}
  {e : Eff}
  {T : Type}
  → ------------------------------
  Γ ⊢[ c ] t :[ e ] T → Distinct Γ

well-typed-distinct (tvar _ _ Hd) = Hd
well-typed-distinct (tlam (Иi As Hcof))
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
well-typed-distinct (tpromote Htype _) = well-typed-distinct Htype
well-typed-distinct (tdemote Htype _) = well-typed-distinct Htype

∈-unique :
  {Γ₂ Γ₁ : TyEnv}
  {x : 𝔸}
  {T T′ : Type}
  (_ : x ∉ dom Γ₁ ∪ dom Γ₂)
  (_ : (x , T) ∈ᴱ Γ₁ , x ∶ T′ & Γ₂)
  → -------------------------------
  T ≡ T′

∈-unique {[]} ∉∪ (here refl) = refl
∈-unique {[]} ∉∪ (there H∈) with () ← ∉→¬∈ (∈-dom H∈)
∈-unique {Γ₂ , x ∶ _} (∉∪ {{q = ∉∪}}) (there H∉) = ∈-unique it H∉
∈-unique {Γ₂ , x ∶ _} (∉∪ {{q = ∉∪ {{p = ∉[]}}}}) (here refl) with () ← ¬≠ x it

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

open LocalClosed
open Body

well-typed-lc :
  {Γ : TyEnv}
  {c : Coeff}
  {t : Term}
  {e : Eff}
  {T : Type}
  → -----------------------------
  Γ ⊢[ c ] t :[ e ] T → lc-at 0 t
well-typed-lc (tvar _ _ _) = lc-at-fvar
well-typed-lc (tlam {t = t} (Иi As Hcof)) = lc-at-op λ
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
well-typed-lc (tpromote Htype _) = well-typed-lc Htype
well-typed-lc (tdemote Htype _) = well-typed-lc Htype

substitution-pres-typing :
  {Γ Γ′ : TyEnv}
  {x : 𝔸}
  {c : Coeff}
  {u t : Term}
  {e : Eff}
  {T₁ T₂ : Type}
  (_ : Γ , x ∶ T₂ ⊢[ c ] t :[ e ] T₁)
  (_ : Γ ⊢[ c ] u :[ det ] T₂)
  → ---------------------------------
  Γ ⊢[ c ] (x => u) t :[ e ] T₁
substitution-pres-typing {Γ} {x = x} {c} {u = u} {T₂ = T₂} Htype Hu =
  go {Γ′ = []} Htype
  where
  go :
    {Γ′ Γ₀ : TyEnv}
    {d : Coeff}
    {t : Term}
    {e : Eff}
    {T₁ : Type}
    {{_ : Γ₀ ≡ Γ , x ∶ T₂ & Γ′}}
    (_ : Γ₀ ⊢[ d ] t :[ e ] T₁)
    → --------------------------------
    Γ & Γ′ ⊢[ d ] (x => u) t :[ e ] T₁
  go {d = d} {{refl}} (tvar {x = x₁} H∈ H≤ Hd) with x ≐ x₁
  ... | equ with refl ← ∈-unique (distinct-∉ Hd) H∈ with c ≤? d
  ...   | yes H≤c =
    weaken-typing
      (tdemote (subst (_ ⊢[ _ ] _ :[ _ ]_) (mul-≤ H≤) Hu) (symm $ m≤′n⇒m⊔′n≡n H≤c))
      (SP.++⁺ˡ _ ⊆-refl)
      (weaken-distinct Hd)
  ...   | no  H≰c =
    weaken-typing
      (weaken-coeff Hu (≤-1 $ ≤+1 $ trich' H≰c))
      (SP.++⁺ˡ _ ⊆-refl)
      (weaken-distinct Hd)
  go {Γ′ = Γ′} {{refl}} (tvar {x = x₁} H∈ H≤ Hd) | neq H≢ with AnyP.++⁻ Γ′ H∈
  ...   | ι₁ H∈₁         = tvar (AnyP.++⁺ˡ   H∈₁) H≤ (weaken-distinct Hd)
  ...   | ι₂ (there H∈₂) = tvar (AnyP.++⁺ʳ _ H∈₂) H≤ (weaken-distinct Hd)
  ...   | ι₂ (here refl) with () ← H≢ refl
  go {Γ′ = Γ′} {{refl}} (tlam {t = t} (Иi As Hcof)) =
    tlam $ Иi (As ∪ [ x ]) λ {y {{∉∪ {{q = H∉}}}} →
      let Heq : (x => u)((0 ~> y) (t ₀)) ≡ (0 ~> y)((x => u) (t ₀))
          Heq = subst-open-comm (t ₀) (symm≠ y x (∉[]₁ H∉)) (lc-at→≻ _ _ $ well-typed-lc Hu)
      in
      subst (λ t → _ ⊢[ _ ] t :[ _ ] _) Heq $ go {Γ′ = Γ′ , y ∶ _} (Hcof y)
    }
  go (tapp Htype Htype₁) = tapp (go Htype) (go Htype₁)
  go {{refl}} (tprim Hϕ Hd Htypes) = tprim Hϕ (weaken-distinct Hd) (go ∘ Htypes)
  go {{refl}} (treal {r = r} Hd) =
    subst (λ ts → _ ⊢[ _ ] op (oreal r , ts) :[ _ ] _) {x = λ()}
      (funext λ ()) (treal (weaken-distinct Hd))
  go {{refl}} (ttup Hd Htypes) = ttup (weaken-distinct Hd) (go ∘ Htypes)
  go (tproj i Htype) = tproj i $ go Htype
  go (tif Htype Htype₁ Htype₂) = tif (go Htype) (go Htype₁) (go Htype₂)
  go (tdiff Hcs Htype Htype₁) = tdiff Hcs (go Htype) (go Htype₁)
  go (tsolve Htype Htype₁ Htype₂) = tsolve (go Htype) (go Htype₁) (go Htype₂)
  go {{refl}} (tdist HD Hd Htypes) = tdist HD (weaken-distinct Hd) (go ∘ Htypes)
  go (tassume Htype) = tassume $ go Htype
  go (tweight Htype) = tweight $ go Htype
  go (texpect Htype) = texpect $ go Htype
  go (tinfer Htype)  = tinfer  $ go Htype
  go (tsub Htype H≤₁ H≤₂) = tsub (go Htype) H≤₁ H≤₂
  go (tpromote Htype refl) = tpromote (go Htype) refl
  go (tdemote Htype refl) = tdemote  (go Htype) refl

-- var-substitution-pres-typing
--   : ∀ {Γ Γ′ x y T₂ t e T₁}
--   → Γ , x ∶ T₂ & Γ′ ⊢ t :[ e ] T₁
--   → -------------------------------------------
--     Γ , y ∶ T₂ & Γ′ ⊢ (x => fvar y) t :[ e ] T₁
-- substitution-pres-typing {Γ′} {x} {u} {T₂} Htype Hu = go Htype
--   where
--   go
--     : ∀ {Γ′ Γ₀ t e T₁}
--     → {{Γ₀ ≡ [ x ∶ T₂ ] & Γ′}}
--     → Γ₀ ⊢ t :[ e ] T₁
--     → -------------------------
--       [] & Γ′ ⊢ (x => u) t :[ e ] T₁
--   go {{Heq}} (tvar {x = x₁})
--     with refl , refl , refl ← single-inv {{Heq}}
--     rewrite dec-equ x = Hu
--   go {Γ′} {{refl}} (tlam {t = t} (Иi As Hcof)) =
--     tlam $ Иi ([ x ] ∪ As) λ { y {{∉∪ {{∉x}}}} →
--       let Heq : (x => u)((0 ~> y) (t ₀)) ≡ (0 ~> y)((x => u) (t ₀))
--           Heq = subst-open-comm (t ₀) (symm≠ y x (∉[]₁ ∉x)) (lc-at→≻ _ _ $ well-typed-lc Hu)
--       in
--       subst (λ x → _ ⊢ x :[ _ ] _) Heq $ go {Γ′ , y ∶ _} (Hcof y)
--     }
--   go (tapp Htype Htype₁) = tapp (go Htype) (go Htype₁)
--   go {{refl}} (tprim Hϕ Hd Htypes) = tprim Hϕ (distinct-weaken Hd) (go ∘ Htypes)
--   go {Γ′} treal with () ← ++-conicalʳ Γ′ _ $ symm it
--   go {{refl}} (ttup Hd Htypes) = ttup (distinct-weaken Hd) (go ∘ Htypes)
--   go (tproj i Htype) = tproj i $ go Htype
--   go (tif Htype Htype₁ Htype₂) =
--     tif (go Htype) (go Htype₁) (go Htype₂)
--   go (tdiff Hcs Htype Htype₁) =
--     tdiff Hcs (go Htype) (go Htype₁)
--   go (tsolve Htype Htype₁ Htype₂) =
--     tsolve (go Htype) (go Htype₁) (go Htype₂)
--   go {{refl}} (tdist HD Hd Htypes) = tdist HD (distinct-weaken Hd) (go ∘ Htypes)
--   go (tassume Htype) = tassume $ go Htype
--   go (tweight Htype) = tweight $ go Htype
--   go (texpect Htype) = texpect $ go Htype
--   go (tinfer Htype)  = tinfer  $ go Htype
--   go {{refl}} (tweaken {Γ′ = Γ₂} {t = t} Htype H⊆ Hd) with x ∈? dom Γ₂
--   ... | yes H∈ with Δ₁ , Δ₂ , [] , H⊆₁ , refl ← ⊆-split (distinct-∉ Hd) H∈ H⊆ =
--     tweaken (go Htype) (++⁺ H⊆₁ []) (distinct-weaken Hd)
--   ... | no H∉ rewrite subst-fresh u t (∉-dom-fv Htype (¬∈→∉ H∉)) =
--     tweaken Htype (⊆-strengthen (¬∈→∉ H∉) H⊆) (distinct-weaken Hd)
--   go (tsub Htype H≤ Hsub) = tsub (go Htype) H≤ Hsub
--   go {{refl}} (tpromote Htype Hmul) = tpromote (go Htype) (all-weaken Hmul)
