open import Lib.Algebra.Reals

module DPPL.Denotations (R : Reals₀) where

open Reals R using (ℝ ; 0r)

open import DPPL.Regularity
open import DPPL.Syntax R hiding (_▸_)
open import DPPL.Typing R

open import Lib.Data.Dec
open import Lib.Data.Finset
open import Lib.Data.Vector
open import Lib.LocallyNameless.Unfinite
open import Lib.Syntax.Env

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Exponential
open import Cat.Diagram.Product.Finite
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Terminal
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Cat.Functor.Hom
open import Cat.Functor.Naturality
open import Cat.Instances.Presheaf.Limits
open import Cat.Instances.Presheaf.Exponentials
open import Data.Dec.Base
open import Data.Fin.Base hiding (_≤_)
open import Data.Power hiding (_∪_)
open import Order.Base
import Cat.Reasoning as CR

open SyntaxVars

open Reg↓≤ using (_≤_ ; ≤-refl ; ≤-trans)

is-const : ℙ (ℝ ^ m → ℝ ^ n)
is-const {n = n} f = elΩ (Σ[ x ∈ ℝ ^ n ] f ≡ λ _ → x)

record DenotAssumptions : Type₁ where
  field
    ⟨_⟩-reg : Coeff → ∀ {m n} → ℙ (ℝ ^ m → ℝ ^ n)
    ⊆-reg : c ≤ c' → ⟨ c' ⟩-reg {m} {n} ⊆ ⟨ c ⟩-reg

    id-reg : (λ x → x) ∈ ⟨ c ⟩-reg {m}
    const-reg : (x : ℝ ^ n) → (λ _ → x) ∈ ⟨ c ⟩-reg {m}
    ∘-reg
      : {m n k : Nat} {f : ℝ ^ n → ℝ ^ k} {g : ℝ ^ m → ℝ ^ n}
      → f ∈ ⟨ c ⟩-reg → g ∈ ⟨ c ⟩-reg → f ⊙ g ∈ ⟨ c ⟩-reg
    -- cond-reg
    --   : (λ a → if a ₀ ≲? 0r then a ₁ else a ₂) ∈ ⟨ P↓ ⟩-reg {3} {1}

  [_,_]-reg : Coeff → Coeff → ∀ {m n} → ℙ (ℝ ^ m → ℝ ^ n)
  [_,_]-reg c d =
    ifᵈ holds? (c ≤ d) then
      ⟨ c ⟩-reg
    else
      is-const

  field
    Prim-denot : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ


module Denotations (Ax : DenotAssumptions) where
  open DenotAssumptions Ax

  open Functor
  open _=>_ renaming (op to opⁿ)
  open CR._≅_

  [,]-reg-≤ : c ≤ c' → [ c , c' ]-reg {m} {n} ≡ ⟨ c ⟩-reg
  [,]-reg-≤ {c = c} {c'} H≤ = ifᵈ-yes (holds? (c ≤ c')) (true-is-yes H≤)

  [,]-reg-≰ : ¬ c ≤ c' → [ c , c' ]-reg {m} {n} ≡ is-const
  [,]-reg-≰ {c = c} {c'} H≰ = ifᵈ-no (holds? (c ≤ c')) (false-is-no H≰)

  id-reg' : c ≤ c' → (λ x → x) ∈ [ c , c' ]-reg {m}
  id-reg' H≤ = subst ((λ x → x) ∈_) (sym $ [,]-reg-≤ H≤) id-reg

  const-reg' : (x : ℝ ^ n) → (λ _ → x) ∈ [ c , c' ]-reg {m}
  const-reg' {c = c} {c'} x with holds? (c ≤ c')
  ... | yes _ = const-reg x
  ... | no  _ = inc (_ , refl)

  ∘-reg'
    : {c d e : Coeff} {m n k : Nat} {f : ℝ ^ n → ℝ ^ k} {g : ℝ ^ m → ℝ ^ n}
    → f ∈ [ d , e ]-reg → g ∈ [ c , d ]-reg → f ⊙ g ∈ [ c , e ]-reg
  ∘-reg' {c} {d} {e} {f = f} {g} Hf Hg with holds? (c ≤ d) | holds? (d ≤ e)
  ... | no c≰d | _ =
    □-rec ([ c , e ]-reg _ .is-tr)
      (λ (x , Hg') → subst (λ g → f ⊙ g ∈ [ c , e ]-reg) (sym Hg') (const-reg' (f x)))
      Hg
  ... | yes c≤d | no d≰e =
    □-rec ([ c , e ]-reg _ .is-tr)
      (λ (x , Hf') → subst (λ f → f ⊙ g ∈ [ c , e ]-reg) (sym Hf') (const-reg' x))
      Hf
  ... | yes c≤d | yes d≤e =
    subst (_ ∈_) (sym $ [,]-reg-≤ (≤-trans c≤d d≤e)) (∘-reg (⊆-reg c≤d _ Hf) Hg)

  module _ where
    open Precategory

    ℛ : Precategory lzero lzero
    ℛ .Ob = Nat × Coeff
    ℛ .Hom (m , c) (n , d) = Σ[ f ∈ (ℝ ^ m → ℝ ^ n) ] f ∈ [ c , d ]-reg
    ℛ .Hom-set _ _ _ _ = hlevel 1
    ℛ .id {m , c} = (λ x → x) , id-reg' ≤-refl
    ℛ ._∘_ (f , Hf) (g , Hg) = f ⊙ g , ∘-reg' Hf Hg
    ℛ .idr f = refl ,ₚ prop!
    ℛ .idl g = refl ,ₚ prop!
    ℛ .assoc f g h = refl ,ₚ prop!

  module ℛ = Precategory ℛ

  ℛ-terminal : Terminal ℛ
  ℛ-terminal = record
    { top  = (0 , A↓)
    ; has⊤ = λ (m , c) → contr
      ((λ _ ()) , const-reg' λ ())
      (λ (x , _) → ext (λ _ ()) ,ₚ is-prop→pathp (λ _ → [ c , A↓ ]-reg _ .is-tr) _ _)
    }

  module ℛ⊤ = Terminal ℛ-terminal

  μ⟨_⟩ : Coeff → Functor ℛ ℛ
  μ⟨ c ⟩ .F₀ (m , d) =
    ifᵈ holds? (d ≤ c) then
      m , d
    else
      ℛ⊤.top
  μ⟨ c ⟩ .F₁ {_ , z} {_ , y} (f , Hf) with holds? (y ≤ c) | holds? (z ≤ c)
  ... | yes _ | yes _ = f , Hf
  ... | yes _ | no _  = (λ _ → f (make 0r)) , const-reg' (f (make 0r))
  ... | no _  | _     = ℛ⊤.!
  μ⟨ c ⟩ .F-id {_ , z} with holds? (z ≤ c)
  ... | yes _ = refl
  ... | no  _ = ℛ⊤.!-unique _
  μ⟨ c ⟩ .F-∘ {_ , z} {_ , y} {_ , x} (f , Hf) (g , Hg)
    with holds? (x ≤ c) | holds? (y ≤ c) | holds? (z ≤ c)
  ... | no _    | _      | _     = ℛ⊤.!-unique _
  ... | yes _   | yes _  | yes _ = refl
  ... | yes _   | yes _  | no  _ =
    refl ,ₚ is-prop→pathp (λ _ → [ A↓ , x ]-reg _ .is-tr) _ _
  ... | yes x≤c | no y≰c | z≤?c
    with f-const ← subst (_ ∈_) ([,]-reg-≰ λ y≤x → y≰c (≤-trans y≤x x≤c)) Hf | z≤?c
  ... | yes _ =
    case f-const of λ x Hf' → funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _)) ,ₚ prop!
  ... | no  _ =
    case f-const of λ x Hf' → funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _)) ,ₚ prop!

  μ-unit : Id => μ⟨ c ⟩
  μ-unit {c} .η (m , x) with holds? (x ≤ c)
  ... | yes _ = ℛ.id
  ... | no  _ = ℛ⊤.!
  μ-unit {c} .is-natural (m , z) (n , y) (f , Hf) with holds? (z ≤ c) | holds? (y ≤ c)
  ... | _      | no  _   = refl ,ₚ is-prop→pathp (λ _ → [ z , A↓ ]-reg _ .is-tr) _ _
  ... | yes _  | yes _   = refl ,ₚ is-prop→pathp (λ _ → [ z , y ]-reg _ .is-tr) _ _
  ... | no z≰c | yes y≤c =
    case f-const of λ x Hf' → funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _)) ,ₚ prop!
    where f-const = subst (_ ∈_) ([,]-reg-≰ λ z≤y → z≰c (≤-trans z≤y y≤c)) Hf

  μ-≤ : c' ≤ c → μ⟨ c ⟩ => μ⟨ c' ⟩
  μ-≤ {c'} {c} H≤ .η (m , x) with holds? (x ≤ c)
  ... | yes _  = μ-unit .η (m , x)
  ... | no x≰c =
    subst (ℛ.Hom ℛ⊤.top)
      (sym $ ifᵈ-no (holds? (x ≤ c')) (false-is-no λ x≤c' → x≰c (≤-trans x≤c' H≤)))
      ℛ⊤.!
  μ-≤ {c'} {c} H≤ .is-natural (m , z) (n , y) (f , Hf) = {!!}
  -- with holds? (z ≤ c) | holds? (y ≤ c)
  -- ... | _ | no y≰c = {!!} -- ℛ⊤.!-unique₂ _ _
  -- ... | no _ | yes _ = {!!}
  -- ... | yes _ | yes _ = μ-unit .is-natural _ _ (f , Hf)

  μ⟨A⟩-Id : μ⟨ A↓ ⟩ ≅ⁿ Id
  μ⟨A⟩-Id = {!!}

  𝔇 : Precategory _ _
  𝔇 = PSh lzero ℛ

  module 𝔇 = Precategory 𝔇

  𝔇-cartesian : Cartesian-category 𝔇
  𝔇-cartesian = PSh-cartesian lzero ℛ

  𝔇-closed : Cartesian-closed 𝔇 𝔇-cartesian
  𝔇-closed = PSh-closed ℛ

  open Cartesian-category 𝔇-cartesian
  open Cartesian-closed 𝔇-closed renaming ([_,_] to _⇒_)

  module 𝔇-ip {n} (F : Fin n → 𝔇.Ob) =
    Indexed-product (Cartesian→standard-finite-products terminal products F)

  □⟨_⟩ : Coeff → Functor 𝔇 𝔇
  □⟨ c ⟩ = precompose (op μ⟨ c ⟩)

  □-counit : □⟨ c ⟩ => Id
  □-counit = {!!}

  □-≤ : c ≤ c' → □⟨ c ⟩ => □⟨ c' ⟩
  □-≤ H≤ .η X = X ▸ opⁿ (μ-≤ H≤)
  □-≤ {c} {c'} H≤ .is-natural _ _ f = Nat-path λ _ → sym $ f .is-natural _ _ _

  □⟨A⟩-Id : □⟨ A↓ ⟩ ≅ⁿ Id
  □⟨A⟩-Id = {!!}

  𝔇ℝ[_] : ℛ.Ob → 𝔇.Ob
  𝔇ℝ[_] = よ₀ ℛ

  Ty-denot : Ty → 𝔇.Ob
  Ty-denot (treal c)            = 𝔇ℝ[ 1 , c ]
  Ty-denot (T₁ ⇒[ c , det ] T₂) = □⟨ c ⟩ .F₀ (Ty-denot T₁ ⇒ Ty-denot T₂)
  Ty-denot (ttup n Ts)          = 𝔇-ip.ΠF λ i → Ty-denot (Ts i)
  -- Distributions are interpreted trivially for the time being.
  Ty-denot (tdist _)          = top
  Ty-denot (_ ⇒[ _ , rnd ] _) = top

  instance
    ⟦⟧-Ty : ⟦⟧-notation Ty
    ⟦⟧-Ty = brackets _ Ty-denot

  open EnvDenot 𝔇-cartesian Ty-denot
  open TypingVars
  open FinsetSyntax

  Sub-denot : T <: T' → Hom ⟦ T ⟧ ⟦ T' ⟧
  Sub-denot (sreal H≤)             = よ₁ ℛ ((λ x → x) , id-reg' H≤)
  Sub-denot (stup {Ts' = Ts'} H<:) =
    𝔇-ip.tuple _ λ i → Sub-denot (H<: i) ∘ 𝔇-ip.π _ i
  Sub-denot (sarr {c = c} {e = det} {det} H<: H<:' H≤c H≤e) =
    □-≤ H≤c .η _ ∘ □⟨ c ⟩ .F₁ ([-,-]₁ _ _ 𝔇-closed (Sub-denot H<:') (Sub-denot H<:))
  Sub-denot (sarr {e' = rnd} H<: H<:' H≤c H≤e) = !
  Sub-denot (sdist H<:)                        = !

  -- env-≤-□ : Γ ≤ c → ⟦ Γ ⟧ ≅ⁿ □⟨ c ⟩ .F₀ ⟦ Γ ⟧
  -- env-≤-□ = ?

  -- ∩ᵗ-is-□ : ⟦ c ∩ᵗ T ⟧ ≡ □⟨ c ⟩ .F₀ ⟦ T ⟧
  -- ∩ᵗ-is-□ = {!!}

  Tm-denot : Γ ⊢ t :[ det ] T → Hom ⟦ Γ ⟧ ⟦ T ⟧
  Tm-denot (tsub {e = det} Hty _ H<:) = Sub-denot H<: ∘ Tm-denot Hty
  Tm-denot (tpromote {Γ = Γ} {Γ' = Γ'} Hty H≤ H⊆) =
    {!!} ∘ env-weaken {Γ} {Γ'} H⊆
  Tm-denot {Γ} (tvar H∈) = env-lookup {Γ = Γ} H∈
  Tm-denot (tlam {e = rnd} Hlam) = !
  Tm-denot {Γ} (tlam {e = det} {T'} (Иi As Hty))
    with (a , H∉) ← fresh{𝔸} (As ∪ env-dom Γ) = □⟨A⟩-Id .from .η _ ∘ ƛ body where
    body = subst (λ Γ → Hom ⟦ Γ ⟧ ⟦ T' ⟧) (env-nub-cons Γ (∉∪₂ As H∉))
      (Tm-denot (Hty a ⦃ ∉∪₁ H∉ ⦄))
  Tm-denot (tapp Hty Hty₁) = ev ∘ ⟨ □-counit .η _ ∘ Tm-denot Hty , Tm-denot Hty₁ ⟩
  Tm-denot (tprim Hϕ Hty) = {!!}
  Tm-denot (treal {r = r}) = {!!} ∘ !
  Tm-denot (ttup Htys) = 𝔇-ip.tuple _ λ i → Tm-denot (Htys i)
  Tm-denot (tproj i Hty) = 𝔇-ip.π _ i ∘ Tm-denot Hty
  Tm-denot (tif Hty Hty₁ Hty₂) = {!!}
  Tm-denot (tinfer Hty) = !
  Tm-denot (tdiff Hty Hty₁ Hc) = {!!}
  Tm-denot (tsolve Hty Hty₁ Hty₂ Hc) = {!!}
