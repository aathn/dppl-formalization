open import 1Lab.Type.Sigma

open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Exponential
open import Cat.Functor.Naturality
open import Cat.Diagram.Comonad
open import Cat.Displayed.Total
open import Cat.Diagram.Monad
open import Cat.Cartesian
open import Cat.Prelude

open import Data.Maybe.Properties
open import Data.Maybe.Base
open import Data.Fin.Base hiding (_≤_)
open import Data.Power hiding (_∩_)

open import Jacana.Denotations.Regularity
open import Jacana.Regularity hiding (A)

open import Lib.Algebra.Reals
open import Lib.Homotopy.Join
open import Lib.Cat.Concrete
open import Lib.Data.Vector
open import Lib.Data.Maybe
open import Lib.Cat.Thin

open import Meta.Idiom

open import Order.Diagram.Meet
open import Order.Base

import Cat.Morphism as Cm

import Jacana.Denotations.Site as Site
import Jacana.Syntax as Syntax

module Jacana.Denotations.Domain (R : Reals₀) (Ax : RegAssumptions R) where

open RegAssumptions Ax
open Cm.Inverses
open Reg⊆-lat hiding (top ; !)
open Functor
open Syntax R
open SyntaxVars
open _=>_
open Site R Ax
open Conc-category ℛ-conc
open Conc-psh ℛ-conc
open Repr-conc (λ x → ℛ-const x , refl)
open CPSh-on
open Cm._≅_
open Reals R using (ℝ)
open Reg≤
open ∫Hom

𝔇 : Precategory _ _
𝔇 = CPSh

module 𝔇 = Precategory 𝔇

𝔇-cartesian : Cartesian-category 𝔇
𝔇-cartesian = CPSh-cartesian

𝔇-closed : Cartesian-closed 𝔇 𝔇-cartesian
𝔇-closed = CPSh-closed

open Cartesian-category 𝔇-cartesian hiding (⟨_,_⟩)
open Cartesian-closed 𝔇-closed using () renaming ([_,_] to _⇒_)
open Inverses

𝔇-ip : ∀ {n} → has-products-indexed-by 𝔇 (Fin n)
𝔇-ip = CPSh-ip

module 𝔇-ip {n} (F : 𝔇.Ob ^ n) = Indexed-product (𝔇-ip F)

record □-factor (X : Reg⊆) (A : ⌞ 𝔇 ⌟) U (f : ∣ U ∣ₒ → ⌞ A ⌟) : Type where
  no-eta-equality
  field
    {reg} : Reg
    {dom} : ⟨ reg ⟩-open-set
    {leg} : ∣ U ∣ₒ → ∣ dom ∣ₛ
    {map} : ∣ dom ∣ₛ → ⌞ A ⌟

    reg-mem : reg ∈ X
    reg-geq : U .fst ≤ reg
    leg-reg : leg ∈ ⟨ U .fst ⟩-reg (U .snd) (⊆-open-set reg-geq dom)
    map-sec : map ∈ A .snd .is-sec (reg , dom)
    factors : f ≡ map ⊙ leg

open □-factor

□⟨_⟩₀ : Reg⊆ → ⌞ 𝔇 ⌟ → ⌞ 𝔇 ⌟
□⟨ X ⟩₀ A .fst = A .fst
□⟨ X ⟩₀ A .snd = cpsh where
  cpsh : CPSh-on ⌞ A ⌟
  cpsh .is-sec U f .∣_∣   = □ (□-factor X A U f) ∗ ∣ is-const f ∣
  cpsh .is-sec U f .is-tr = hlevel 1
  cpsh .is-sec-∘ f h Hf₀  = case h .snd of λ where
    (inr H⋆)        → case H⋆ of λ _ _ p → inr (inc (_ , ap (f ⊙_) p))
    (inl (H≤ , Hh)) → case Hf₀ of λ where
      (inr H⋆) → case H⋆ of λ _ p → inr (inc (_ , ap (_⊙ ∣ h ∣ₕ) p))
      (inl Hf) → inl $ flip □-map Hf λ fac → record
        { reg-mem = fac .reg-mem
        ; reg-geq = ≤-trans H≤ (fac .reg-geq)
        ; leg-reg = coerce-reg (∘-reg (⊆-reg H≤ (fac .leg) (fac .leg-reg)) Hh)
        ; map-sec = fac .map-sec
        ; factors = ap (_⊙ ∣ h ∣ₕ) (fac .factors)
        }
  cpsh .pt-sec x = inr (inc (_ , refl))

□⟨_⟩ : Reg⊆ → Functor 𝔇 𝔇
□⟨ X ⟩ .F₀                        = □⟨ X ⟩₀
□⟨ X ⟩ .F₁ f .fst                 = f .fst
□⟨ X ⟩ .F₁ (∫hom f Hf) .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , ap (f ⊙_) p))
  (inl Hg) → inl $ flip □-map Hg λ fac → record
    { reg-mem = fac .reg-mem
    ; reg-geq = fac .reg-geq
    ; leg-reg = fac .leg-reg
    ; map-sec = Hf _ (fac .map-sec)
    ; factors = ap (f ⊙_) (fac .factors)
    }
□⟨ X ⟩ .F-id    = ext λ _ → refl
□⟨ X ⟩ .F-∘ f g = ext λ _ → refl

□-counit : □⟨ X ⟩ => Id
□-counit .η A .fst x     = x
□-counit .η A .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → const-sec A p
  (inl Hg) → case Hg of λ fac →
    subst (λ x → ∣ A .snd .is-sec _ x ∣) (sym (fac .factors))
    $ A .snd .is-sec-∘ _ (_ , inl (fac .reg-geq , fac .leg-reg)) (fac .map-sec)
□-counit .is-natural _ _ _ = ext λ _ → refl

□-comult : □⟨ X ∩ X' ⟩ => □⟨ X ⟩ F∘ □⟨ X' ⟩
□-comult .η A .fst x     = x
□-comult .η A .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , p))
  (inl Hg) → inl $ flip □-map Hg λ fac → record
    { reg-mem = fac .reg-mem .fst
    ; reg-geq = fac .reg-geq
    ; leg-reg = fac .leg-reg
    ; map-sec = inl
      ( inc record
        { reg-mem = fac .reg-mem .snd
        ; reg-geq = ≤-refl
        ; leg-reg = coerce-reg id-reg
        ; map-sec = fac .map-sec
        ; factors = refl
        }
      )
    ; factors = fac .factors
    }
□-comult .is-natural _ _ _ = ext λ _ → refl

□-comult-base : □⟨ X ⟩ => □⟨ X ⟩ F∘ □⟨ X ⟩
□-comult-base {X} = subst (λ Z → □⟨ Z ⟩ => □⟨ X ⟩ F∘ □⟨ X ⟩) ∩-idem □-comult

□-is-comonad : is-comonad □-counit (□-comult-base {X})
□-is-comonad .is-comonad.δ-unitl = ext λ _ → transport-refl _ ∙ transport-refl _
□-is-comonad .is-comonad.δ-unitr = ext λ _ → transport-refl _ ∙ transport-refl _
□-is-comonad .is-comonad.δ-assoc = ext λ _ → refl

□-comult' : X ~ʳ X' → □⟨ X ⟩ F∘ □⟨ X' ⟩ => □⟨ X ∩ X' ⟩
□-comult' H~ .η A .fst x                  = x
□-comult' {X} {X'} H~ .η A .snd {U} g Hg₀ = case Hg₀ of λ where
  (inr H⋆)  → inr H⋆
  (inl Hg₁) → case Hg₁ of λ fac → case fac .map-sec of λ where
    (inr H⋆)  → case H⋆ of λ x p → inr (inc (_ , fac .factors ∙ ap (_⊙ fac .leg) p))
    (inl Hg₂) → case Hg₂ of λ fac' →
      case H~ (_ , fac .reg-mem) (_ , fac' .reg-mem) of λ H∩ →
      flip (∥-∥-elim (λ _ → hlevel 1)) (H∩ (fac' .reg-geq)) λ (z , x≤z , z≤y) → inl
        ( inc record
          { reg-mem = z .snd
          ; reg-geq = ≤-trans (fac .reg-geq) x≤z
          ; leg-reg = coerce-reg
            $ ∘-reg (⊆-reg (fac .reg-geq) _ (fac' .leg-reg)) (fac .leg-reg)
          ; map-sec = A .snd .is-sec-∘ _ (ℛ-id≤ z≤y) (fac' .map-sec)
          ; factors = fac .factors ∙ ap (_⊙ fac .leg) (fac' .factors)
          }
        )
□-comult' H~ .is-natural _ _ _ = ext λ _ → refl

□-comult-≅ : X ~ʳ X' → □⟨ X ∩ X' ⟩ ≅ⁿ □⟨ X ⟩ F∘ □⟨ X' ⟩
□-comult-≅ HX .to             = □-comult
□-comult-≅ HX .from           = □-comult' HX
□-comult-≅ HX .inverses .invl = ext λ _ _ → refl
□-comult-≅ HX .inverses .invr = ext λ _ _ → refl

□-⊆ : X ⊆ X' → □⟨ X ⟩ => □⟨ X' ⟩
□-⊆ H⊆ .η A .fst x     = x
□-⊆ H⊆ .η A .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → inr H⋆
  (inl Hg) → inl $ flip □-map Hg λ fac →
    record { □-factor fac ; reg-mem = H⊆ _ (fac .reg-mem) }
□-⊆ H⊆ .is-natural _ _ _ = ext λ _ → refl

□-top : □⟨ X ⟩₀ top ≅ top
□-top .to             = !
□-top .from .fst      = _
□-top .from .snd _ _  = inr (inc (_ , refl))
□-top .inverses .invl = ext λ _ → refl
□-top .inverses .invr = ext λ _ → refl

□-prod : ∀ {A B} → Hom (□⟨ X ⟩₀ (A ⊗₀ B)) (□⟨ X ⟩₀ A ⊗₀ □⟨ X ⟩₀ B)
□-prod .fst x     = x
□-prod .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x y p →
    inr (inc (_ , ap (fst ⊙_) p)) , inr (inc (_ , ap (snd ⊙_) p))
  (inl Hg) → case Hg of λ fac → inl
    ( inc record
      { □-factor fac ; map = _
      ; map-sec = fac .map-sec .fst
      ; factors = ap (fst ⊙_) (fac .factors)
      }
    ) , inl
    ( inc record
      { □-factor fac ; map = _
      ; map-sec = fac .map-sec .snd
      ; factors = ap (snd ⊙_) (fac .factors)
      }
    )

□-prod' : is-meet-closed X → ∀ {A B} → Hom (□⟨ X ⟩₀ A ⊗₀ □⟨ X ⟩₀ B) (□⟨ X ⟩₀ (A ⊗₀ B))
□-prod' HX .fst x                          = x
□-prod' {X} HX {A} {B} .snd g (Hg₀ , Hg₀') = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → case Hg₀' of λ where
    (inr H⋆') → case H⋆' of λ y q → inr (inc (_ , ap₂ ⟨_,_⟩ p q))
    (inl Hg') → inl $ flip □-map Hg' λ fac → record
      { □-factor fac ; map = _
      ; map-sec = A .snd .pt-sec x , fac .map-sec
      ; factors = ap₂ ⟨_,_⟩ p (fac .factors)
      }
  (inl Hg) → case Hg of λ fac → case Hg₀' of λ where
    (inr H⋆') → case H⋆' of λ x q → inl
      ( inc record
        { □-factor fac ; map = _
        ; map-sec = fac .map-sec , B .snd .pt-sec x
        ; factors = ap₂ ⟨_,_⟩ (fac .factors) q
        }
      )
    (inl Hg') → case Hg' of λ fac' →
      case HX (_ , fac .reg-mem) (_ , fac' .reg-mem) of λ where
        (inl W-incompat)   → absurd (W-incompat _ (fac .reg-geq) (fac' .reg-geq))
        (inr (glb , Hglb)) → inl
          ( let module G = Meet glb in
            inc record
            { reg-mem = Hglb
            ; reg-geq = G.greatest _ (fac .reg-geq) (fac' .reg-geq)
            ; leg-reg = coerce-reg (tup-reg (fac .leg-reg) (fac' .leg-reg))
            ; map-sec =
                A .snd .is-sec-∘ _ (_ , inl (G.meet≤l , proj-reg₁)) (fac .map-sec)
              , B .snd .is-sec-∘ _ (_ , inl (G.meet≤r , proj-reg₂)) (fac' .map-sec)
            ; factors =
                ap₂ ⟨_,_⟩ (fac .factors) (fac' .factors)
              ∙ ap (λ z → ×-map (fac .map) (fac' .map) ⊙ z ⊙ ⟨ fac .leg , fac' .leg ⟩)
                (sym $ funext $ Equiv.η $ ×ₛ-≃
                  (⊆-open-set G.meet≤l (fac .dom)) (⊆-open-set G.meet≤r (fac' .dom)))
            }
          )

□-prod-≅ : is-meet-closed X → ∀ {A B} → □⟨ X ⟩₀ (A ⊗₀ B) ≅ (□⟨ X ⟩₀ A ⊗₀ □⟨ X ⟩₀ B)
□-prod-≅ HX .to             = □-prod
□-prod-≅ HX .from           = □-prod' HX
□-prod-≅ HX .inverses .invl = ext λ _ _ → refl
□-prod-≅ HX .inverses .invr = ext λ _ _ → refl

□⟨⊤⟩-Id : Id => □⟨ Reg⊆-lat.top ⟩
□⟨⊤⟩-Id .η A .fst x        = x
□⟨⊤⟩-Id .η A .snd {U} g Hg = inl
  ( inc record
    { reg-mem = tt
    ; reg-geq = ≤-refl
    ; leg-reg = coerce-reg id-reg
    ; map-sec = Hg
    ; factors = refl
    }
  )
□⟨⊤⟩-Id .is-natural _ _ _  = ext λ _ → refl

𝔇ℝ[_] : Reg↓ → 𝔇.Ob
𝔇ℝ[ c ] .fst = el! ℝ
𝔇ℝ[ c ] .snd = cpsh where
  cpsh : CPSh-on _
  cpsh .is-sec (r , U) f .∣_∣ =
    (r ∈ c × f' ∈ ⟨ r ⟩-reg U (ℝ-open-set 1)) ∗ ∣ is-const f ∣
    where f' = ⟨ make ⊙ f , _ ⟩
  cpsh .is-sec U f .is-tr = hlevel 1
  cpsh .is-sec-∘ g h Hg   = case h .snd of λ where
    (inr H⋆)        → case H⋆ of λ _ _ p → inr (inc (_ , ap (g ⊙_) p))
    (inl (H≤ , Hh)) → case Hg of λ where
      (inr H⋆)         → case H⋆ of λ _ p → inr (inc (_ , ap (_⊙ h .fst) p))
      (inl (HU , Hg')) → inl (c .pres-≤ H≤ HU , coerce-reg (∘-reg (⊆-reg H≤ _ Hg') Hh))
  cpsh .pt-sec x = inr (inc (x , refl))

□-𝔇ℝ : □⟨ X ⟩₀ 𝔇ℝ[ c ] ≅ 𝔇ℝ[ Close-downward · (X ∩ c .hom) ]
□-𝔇ℝ .to .fst x                     = x
□-𝔇ℝ {c = c} .to .snd {r , U} g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , p))
  (inl Hg) → case Hg of λ fac → case fac .map-sec of λ where
    (inr H⋆) → case H⋆ of λ x q → inr (inc (_ , fac .factors ∙ ap (_⊙ fac .leg) q))
    (inl (Hc , Hreg)) → inl
      ( inc (_ , fac .reg-geq , fac .reg-mem , Hc)
      , subst (λ f → ∣ ⟨ r ⟩-reg U (ℝ-open-set 1) f ∣)
        (ap (λ f → ⟨ make ⊙ f , _ ⟩) (sym (fac .factors)))
        (coerce-reg (∘-reg (⊆-reg (fac .reg-geq) _ Hreg) (fac .leg-reg)))
      )
□-𝔇ℝ .from .fst x                = x
□-𝔇ℝ {X} {c} .from .snd {U} g Hg = case Hg of λ where
  (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , ext λ z Hz → p $ₚ (z , Hz)))
  (inl (HU , Hreg)) → inl $ flip □-map HU λ (z , U≤z , Hz , Hz') → record
    { reg-mem = Hz
    ; reg-geq = U≤z
    ; leg-reg = coerce-reg Hreg
    ; map-sec = inl
      ( Hz'
      , subst (λ f → ∣ ⟨ z ⟩-reg (ℝ-open-set 1) (ℝ-open-set 1) f ∣)
        (ext λ _ _ → Σ-prop-path! (funext $ Fin-cases refl λ ())) id-reg
      )
    ; factors = refl
    }
□-𝔇ℝ .inverses .invl = ext λ _ → refl
□-𝔇ℝ .inverses .invr = ext λ _ → refl

𝔇ℝ-≤ : c ⊆ c' → Hom 𝔇ℝ[ c ] 𝔇ℝ[ c' ]
𝔇ℝ-≤ H≤ .fst x = x
𝔇ℝ-≤ H≤ .snd g Hg = case Hg of λ where
  (inr H⋆)   → inr H⋆
  (inl Hreg) → inl (H≤ _ (Hreg .fst) , Hreg .snd)

𝔇ℝ-const : ℝ → Hom top 𝔇ℝ[ c ]
𝔇ℝ-const r .fst _       = r
𝔇ℝ-const {c} r .snd _ _ = 𝔇ℝ[ c ] .snd .pt-sec r

𝔇ℝ'[_] : Reg↓ ^ n → 𝔇.Ob
𝔇ℝ'[ cs ] = 𝔇-ip.ΠF λ i → 𝔇ℝ[ cs i ]

record LM-factor (A : ⌞ 𝔇 ⌟) U (f : ∣ U ∣ₒ → Maybe ⌞ A ⌟) : Type where
  no-eta-equality
  field
    {dom}      : ℙ (ℝ ^ U .snd .dim)
    {map}      : ∫ₚ dom → ⌞ A ⌟
    {dom-open} : ∣ ⟨ U .fst ⟩-open dom ∣
    {dom-sub}  : dom ⊆ U .snd .set

    map-sec  : ∣ A .snd .is-sec (_ , mk-open-set dom-open) map ∣
    just-dom : ∀ {x y} → f x ≡ just y → x .fst ∈ dom
    dom-just : just ⊙ map ≡ f ⊙ ⟨ fst , dom-sub _ ⊙ snd ⟩

open LM-factor

LM₀ : ⌞ 𝔇 ⌟ → ⌞ 𝔇 ⌟
LM₀ A .fst = el! (Maybe ⌞ A ⌟)
LM₀ A .snd = cpsh where
  cpsh : CPSh-on _
  cpsh .is-sec U f .∣_∣          = □ (LM-factor A U f) ∗ ∣ is-const f ∣
  cpsh .is-sec U f .is-tr        = hlevel 1
  cpsh .is-sec-∘ {U} {V} f h Hf₀ = case h .snd of λ where
    (inr H⋆)          → case H⋆ of λ x Hx p → inr (inc (_ , ap (f ⊙_) p))
    (inl (H≤ , Hreg)) → case Hf₀ of λ where
      (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , ap (_⊙ ∣ h ∣ₕ) p))
      (inl Hf) → inl $ flip □-map Hf λ fac →
        let g' = pb-projₛ (U .snd) (⊆-open-set H≤ (V .snd)) ∣ h ∣ₕ (fac .dom) in
        record
        { map-sec = A .snd .is-sec-∘ (fac .map)
          (g' , inl (H≤ , pb-proj-reg Hreg (⊆-open H≤ _ (fac .dom-open))))
          (fac .map-sec)
        ; just-dom = λ q → inc (_ , fac .just-dom q)
        ; dom-just = ap (_⊙ g') (fac .dom-just) ∙ ext λ _ _ → ap f (Σ-prop-path! refl)
        }
  cpsh .pt-sec x = inr (inc (x , refl))

LM : Functor 𝔇 𝔇
LM .F₀                        = LM₀
LM .F₁ f .fst                 = Map-Maybe .map (f .fst)
LM .F₁ (∫hom f Hf) .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , ap (Map-Maybe .map f ⊙_) p))
  (inl Hg) → inl $ flip □-map Hg λ fac → record
    { map-sec  = Hf (fac .map) (fac .map-sec)
    ; just-dom = λ q → fac .just-dom (map-just' q .snd .fst)
    ; dom-just = ext λ x Hx → sym (map-just (sym (fac .dom-just $ₚ (x , Hx))))
    }
LM .F-id    = ext map-id
LM .F-∘ f g = ext map-∘

LM-unit : Id => LM
LM-unit .η A .fst      = just
LM-unit .η A .snd g Hg = inl
  ( inc record
    { map-sec  = Hg
    ; just-dom = λ {x} _ → x .snd
    ; dom-just = refl
    }
  )
LM-unit .is-natural _ _ _ = ext λ _ → refl

LM-mult : LM F∘ LM => LM
LM-mult .η A .fst       = maybe-join
LM-mult .η A .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆)  → case H⋆ of λ x p → inr (inc (_ , ap (maybe-join ⊙_) p))
  (inl Hg₁) → case Hg₁ of λ fac → case fac .map-sec of λ where
    (inr H⋆) → case H⋆ of λ where
      nothing p → inr
        ( inc
          ( nothing
          , ext λ x Hx → join-nothing λ {y} q → just-inj $
            just y            ≡⟨ q ⟩
            g (x , Hx)        ≡⟨ ap (λ H → g (x , H)) prop! ⟩
            g (x , _)         ≡˘⟨ fac .dom-just $ₚ (x , fac .just-dom (sym q)) ⟩
            just (fac .map _) ≡⟨ ap just (p $ₚ _) ⟩
            just nothing      ∎
          )
        )
      (just x) p → inl
        ( inc record
          { map-sec  = A .snd .pt-sec {_ , mk-open-set (fac .dom-open)} x
          ; just-dom = λ q → fac .just-dom (join-just-inv q)
          ; dom-just = sym p ∙ ap (maybe-join ⊙_) (fac .dom-just)
          }
        )
    (inl Hg) → inl $ flip □-map Hg λ fac' → record
      { map-sec = fac' .map-sec
      ; just-dom = λ {x} {y} p →
        let p' = join-just-inv p in
        fac' .just-dom $ just-inj $
          just (fac .map _) ≡⟨ fac .dom-just $ₚ (x .fst , fac .just-dom p') ⟩
          g (x .fst , _)    ≡⟨ ap (λ H → g (_ , H)) prop! ⟩
          g x               ≡⟨ p' ⟩
          just (just y)     ∎
      ; dom-just =
          ap ((maybe-join ⊙ just) ⊙_) (fac' .dom-just)
        ∙ ap (λ x → maybe-join ⊙ x ⊙ ⟨ _ , fac' .dom-sub _ ⊙ snd ⟩) (fac .dom-just)
      }
LM-mult .is-natural _ _ _ = ext (happly join-nat)

LM-is-monad : is-monad LM-unit LM-mult
LM-is-monad .is-monad.μ-unitr = ext (happly join-unitr)
LM-is-monad .is-monad.μ-unitl = ext (happly join-unitl)
LM-is-monad .is-monad.μ-assoc = ext (happly join-assoc)

□-LM : □⟨ X ⟩ F∘ LM => LM F∘ □⟨ X ⟩
□-LM .η A .fst x             = x
□-LM .η A .snd {_ , U} g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → inr H⋆
  (inl Hg₁) → case Hg₁ of λ fac → case fac .map-sec of λ where
    (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , fac .factors ∙ ap (_⊙ fac .leg) p))
    (inl Hg) → case Hg of λ fac' → inl
      ( let
          V  = ⊆-open-set (fac .reg-geq) (fac .dom)
          U' = pbₛ U V (fac .leg) (fac' .dom)
        in inc record
        { dom-sub = pb-⊆ U V (fac .leg) (fac' .dom)
        ; map-sec = inl
          ( inc record
            { reg-mem = fac .reg-mem
            ; reg-geq = fac .reg-geq
            ; leg-reg =
              pb-proj-reg (leg-reg fac) (⊆-open (reg-geq fac) _ (fac' .dom-open))
            ; map-sec = fac' .map-sec
            ; factors = refl
            }
          )
        ; just-dom = λ {x} p →
          inc (_ , fac' .just-dom (sym (ap (_$ x) (fac .factors)) ∙ p))
        ; dom-just =
            ap (_⊙ pb-projₛ U V (fac .leg) (fac' .dom)) (fac' .dom-just)
          ∙ ext (λ _ _ → ap (fac .map) (Σ-prop-path! refl))
          ∙ sym (ap (_⊙ (λ (x : ∫ₚ U') → _)) (fac .factors))
        }
      )
□-LM .is-natural _ _ _ = ext λ _ → refl
