open import Lib.Algebra.Reals

module DPPL.Denotations (R : Reals₀) where

open Reals R using (ℝ ; 0r)

open import DPPL.Regularity hiding (A;P;C;M)
open import DPPL.Syntax R hiding (_▸_)
open import DPPL.Typing R

open import Lib.Cat.Concrete
open import Lib.Cat.Functor
open import Lib.Cat.Subcategory
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
open import Cat.Functor.Subcategory
open import Data.Dec.Base
open import Data.Fin.Base hiding (_≤_)
open import Data.Power hiding (_∪_)
open import Order.Base
open import Order.Lattice
import Cat.Reasoning as CR
import Cat.Functor.Reasoning as FR

open SyntaxVars

open Reg↓≤ using (_≤_ ; ≤-refl ; ≤-trans)
private module RL = is-lattice Reg↓-lattice

is-const : ℙ (ℝ ^ m → ℝ ^ n)
is-const {n = n} f = elΩ (Σ[ x ∈ ℝ ^ n ] f ≡ λ _ → x)

π'[_] : Fin m → ℝ ^ m → ℝ ^ 1
π'[ i ] = make ⊙ π[ i ]

π'1 : {f : ℝ ^ m → ℝ ^ 1} → π'[ fzero ] ⊙ f ≡ f
π'1 {f = f} = ext λ _ → Fin-cases refl λ ()

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

  ⟨_∣_⟩-reg : Coeff → Coeff → ∀ {m n} → ℙ (ℝ ^ m → ℝ ^ n)
  ⟨_∣_⟩-reg c d =
    ifᵈ holds? (c ≤ d) then
      ⟨ c ⟩-reg
    else
      is-const

  ⟨_⟩-sec : Coeff ^ n → ∀ {m} → Coeff → ℙ (ℝ ^ m → ℝ ^ n)
  ⟨ cs ⟩-sec c g = elΩ $ ∀ i → π'[ i ] ⊙ g ∈ ⟨ c ∣ cs i ⟩-reg

  ⟨_∥_⟩-reg : Coeff ^ m → Coeff ^ n → ℙ (ℝ ^ m → ℝ ^ n)
  ⟨_∥_⟩-reg {m} {n} cs cs' f = elΩ $
    ∀ {k : Nat} {c : Coeff} (g : ℝ ^ k → ℝ ^ m)
    → g ∈ ⟨ cs ⟩-sec c → f ⊙ g ∈ ⟨ cs' ⟩-sec c

  field
    Prim-denot : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ ^ 1
    Prim-reg
      : {cs : Coeff ^ PrimAr ϕ} → PrimTy ϕ ≡ (cs , c)
      → Prim-denot ϕ ∈ ⟨ cs ∥ make c ⟩-reg


module Denotations (Ax : DenotAssumptions) where
  open DenotAssumptions Ax

  open Functor
  open _=>_ renaming (op to opⁿ)
  open Subcat-hom
  open CR._≅_
  open CR.Inverses

  ⟨∣⟩-reg-≤ : c ≤ c' → ⟨ c ∣ c' ⟩-reg {m} {n} ≡ ⟨ c ⟩-reg
  ⟨∣⟩-reg-≤ {c = c} {c'} H≤ = ifᵈ-yes (holds? (c ≤ c')) (true→is-yes H≤)

  ⟨∣⟩-reg-≰ : ¬ c ≤ c' → ⟨ c ∣ c' ⟩-reg {m} {n} ≡ is-const
  ⟨∣⟩-reg-≰ {c = c} {c'} H≰ = ifᵈ-no (holds? (c ≤ c')) (false→is-no H≰)

  id-reg' : c ≤ c' → (λ x → x) ∈ ⟨ c ∣ c' ⟩-reg {m}
  id-reg' H≤ = subst ((λ x → x) ∈_) (sym $ ⟨∣⟩-reg-≤ H≤) id-reg

  const-reg' : (x : ℝ ^ n) → (λ _ → x) ∈ ⟨ c ∣ c' ⟩-reg {m}
  const-reg' {c = c} {c'} x with holds? (c ≤ c')
  ... | yes _ = const-reg x
  ... | no  _ = inc (_ , refl)

  ∘-reg'
    : {c d e : Coeff} {m n k : Nat} {f : ℝ ^ n → ℝ ^ k} {g : ℝ ^ m → ℝ ^ n}
    → f ∈ ⟨ d ∣ e ⟩-reg → g ∈ ⟨ c ∣ d ⟩-reg → f ⊙ g ∈ ⟨ c ∣ e ⟩-reg
  ∘-reg' {c} {d} {e} {f = f} {g} Hf Hg with holds? (c ≤ d) | holds? (d ≤ e)
  ... | no c≰d | _ =
    □-rec (⟨ c ∣ e ⟩-reg _ .is-tr)
      (λ (x , Hg') → subst (λ g → f ⊙ g ∈ ⟨ c ∣ e ⟩-reg) (sym Hg') (const-reg' (f x)))
      Hg
  ... | yes c≤d | no d≰e =
    □-rec (⟨ c ∣ e ⟩-reg _ .is-tr)
      (λ (x , Hf') → subst (λ f → f ⊙ g ∈ ⟨ c ∣ e ⟩-reg) (sym Hf') (const-reg' x))
      Hf
  ... | yes c≤d | yes d≤e =
    subst (_ ∈_) (sym $ ⟨∣⟩-reg-≤ (≤-trans c≤d d≤e)) (∘-reg (⊆-reg c≤d _ Hf) Hg)

  module _ where
    open Precategory

    ℛ : Precategory lzero lzero
    ℛ .Ob = Nat × Coeff
    ℛ .Hom (m , c) (n , d) = Σ[ f ∈ (ℝ ^ m → ℝ ^ n) ] f ∈ ⟨ c ∣ d ⟩-reg
    ℛ .Hom-set _ _ _ _ = hlevel 1
    ℛ .id {m , c} = (λ x → x) , id-reg' ≤-refl
    ℛ ._∘_ (f , Hf) (g , Hg) = f ⊙ g , ∘-reg' Hf Hg
    ℛ .idr f = refl ,ₚ prop!
    ℛ .idl g = refl ,ₚ prop!
    ℛ .assoc f g h = refl ,ₚ prop!

  module ℛ = CR ℛ

  ℛ-terminal : Terminal ℛ
  ℛ-terminal = record
    { top  = (0 , A↓)
    ; has⊤ = λ (m , c) → contr
      ((λ _ ()) , const-reg' λ ())
      (λ (x , _) → ext (λ _ ()) ,ₚ is-prop→pathp (λ _ → ⟨ c ∣ A↓ ⟩-reg _ .is-tr) _ _)
    }

  module ℛ⊤ = Terminal ℛ-terminal

  ℛ-id≤ : c ≤ c' → ℛ.Hom (m , c) (m , c')
  ℛ-id≤ H≤ = (λ x → x) , id-reg' H≤

  ℛ-const : ℝ ^ m → ℛ.Hom ℛ⊤.top (m , c)
  ℛ-const x = (λ _ → x) , const-reg' x

  ℛ-conc : Conc-category ℛ
  ℛ-conc .Conc-category.terminal          = ℛ-terminal
  ℛ-conc .Conc-category.⋆-hom-faithful H≡ =
    funext (λ z → ap fst (H≡ $ₚ ℛ-const z) $ₚ make 0r) ,ₚ prop!

  μ⟨_⟩ : Coeff → Functor ℛ ℛ
  μ⟨ c ⟩ .F₀ (m , d) =
    ifᵈ holds? (d ≤ c) then
      m , d
    else
      ℛ⊤.top
  μ⟨ c ⟩ .F₁ {_ , z} {_ , y} (f , Hf) with holds? (y ≤ c) | holds? (z ≤ c)
  ... | yes _ | yes _ = f , Hf
  ... | yes _ | no _  = ℛ-const (f (make 0r))
  ... | no _  | _     = ℛ⊤.!
  μ⟨ c ⟩ .F-id {_ , z} with holds? (z ≤ c)
  ... | yes _ = refl
  ... | no  _ = ℛ⊤.!-unique _
  μ⟨ c ⟩ .F-∘ {_ , z} {_ , y} {_ , x} (f , Hf) (g , Hg)
    with holds? (x ≤ c) | holds? (y ≤ c) | holds? (z ≤ c)
  ... | no _    | _      | _     = ℛ⊤.!-unique _
  ... | yes _   | yes _  | yes _ = refl
  ... | yes _   | yes _  | no  _ =
    refl ,ₚ is-prop→pathp (λ _ → ⟨ A↓ ∣ x ⟩-reg _ .is-tr) _ _
  ... | yes x≤c | no y≰c | z≤?c
    with f-const ← subst (_ ∈_) (⟨∣⟩-reg-≰ λ y≤x → y≰c (≤-trans y≤x x≤c)) Hf | z≤?c
  ... | yes _ =
    case f-const of λ x Hf' → funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _)) ,ₚ prop!
  ... | no  _ =
    case f-const of λ x Hf' → funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _)) ,ₚ prop!

  μ-pres-top : μ⟨ c ⟩ .F₀ ℛ⊤.top ≡ ℛ⊤.top
  μ-pres-top {c = c} with holds? (A↓ ≤ c)
  ... | yes _ = refl
  ... | no  _ = refl

  μ-onto-points : ∀ {U} → is-surjective (μ⟨ c ⟩ .F₁ {ℛ⊤.top} {U})
  μ-onto-points {c = c} {n , c'} (f , Hf) with holds? (A↓ ≤ c) | holds? (c' ≤ c)
  ... | _       | no  _    = inc (ℛ-const (make 0r) , ℛ⊤.!-unique _)
  ... | yes _   | yes _    = inc ((f , Hf) , refl)
  ... | no  A≰c | yes c'≤c = case f-const of λ x Hf' →
    inc ((f , Hf) , funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _)) ,ₚ prop!)
    where f-const = subst (f ∈_) (⟨∣⟩-reg-≰ λ A≤c' → A≰c (≤-trans A≤c' c'≤c)) Hf

  μ-unit : Id => μ⟨ c ⟩
  μ-unit {c} .η (m , x) with holds? (x ≤ c)
  ... | yes _ = ℛ.id
  ... | no  _ = ℛ⊤.!
  μ-unit {c} .is-natural (m , z) (n , y) (f , Hf) with holds? (z ≤ c) | holds? (y ≤ c)
  ... | _      | no  _   = refl ,ₚ is-prop→pathp (λ _ → ⟨ z ∣ A↓ ⟩-reg _ .is-tr) _ _
  ... | yes _  | yes _   = refl ,ₚ is-prop→pathp (λ _ → ⟨ z ∣ y ⟩-reg _ .is-tr) _ _
  ... | no z≰c | yes y≤c =
    case f-const of λ x Hf' → funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _)) ,ₚ prop!
    where f-const = subst (_ ∈_) (⟨∣⟩-reg-≰ λ z≤y → z≰c (≤-trans z≤y y≤c)) Hf

  μ-≤ : c' ≤ c → μ⟨ c ⟩ => μ⟨ c' ⟩
  μ-≤ {c'} {c} H≤ .η (m , x) with holds? (x ≤ c)
  ... | yes _ = μ-unit .η (m , x)
  ... | no x≰c with holds? (x ≤ c')
  ... | yes x≤c' = absurd (x≰c (≤-trans x≤c' H≤))
  ... | no _     = ℛ⊤.!
  μ-≤ {c'} {c} H≤ .is-natural (m , z) (n , y) (f , Hf)
    with holds? (z ≤ c) | holds? (y ≤ c)
  ... | yes _    | yes _ = μ-unit .is-natural _ _ (f , Hf)
  ... | no z≰c   | yes _ with holds? (z ≤ c') | holds? (y ≤ c')
  ... | yes z≤c' | _     = absurd (z≰c (≤-trans z≤c' H≤))
  ... | _        | no _  = ℛ⊤.!-unique₂ _ _
  ... | no _     | yes _ = ℛ.idl _ ∙ ℛ.intror (ℛ⊤.!-unique _)
  μ-≤ {c'} {c} H≤ .is-natural _ (n , y) _ | _ | no y≰c with holds? (y ≤ c')
  ... | yes y≤c' = absurd (y≰c (≤-trans y≤c' H≤))
  ... | no _     = ℛ⊤.!-unique₂ _ _

  μ⟨A⟩-Id : μ⟨ A↓ ⟩ ≅ⁿ Id
  μ⟨A⟩-Id = to-natural-iso ni where
    ni : make-natural-iso μ⟨ A↓ ⟩ Id
    ni .make-natural-iso.eta (m , c) with holds? (c ≤ A↓)
    ... | yes _   = ℛ.id
    ... | no  c≰A = absurd (c≰A (subst (c ≤_) A↓-is-top RL.!))
    ni .make-natural-iso.inv (m , c) with holds? (c ≤ A↓)
    ... | yes _   = ℛ.id
    ... | no  c≰A = absurd (c≰A (subst (c ≤_) A↓-is-top RL.!))
    ni .make-natural-iso.eta∘inv (m , c) with holds? (c ≤ A↓)
    ... | yes _   = ℛ.idl _
    ... | no  c≰A = absurd (c≰A (subst (c ≤_) A↓-is-top RL.!))
    ni .make-natural-iso.inv∘eta (m , c) with holds? (c ≤ A↓)
    ... | yes _   = ℛ.idl _
    ... | no  c≰A = absurd (c≰A (subst (c ≤_) A↓-is-top RL.!))
    ni .make-natural-iso.natural (m , c) (n , c') f
      with holds? (c ≤ A↓) | holds? (c' ≤ A↓)
    ... | no c≰A | _       = absurd (c≰A (subst (c ≤_) A↓-is-top RL.!))
    ... | _      | no c'≰A = absurd (c'≰A (subst (c' ≤_) A↓-is-top RL.!))
    ... | yes _  | yes _   = ℛ.id-comm

  𝔇 : Precategory _ _
  𝔇 = ConcPSh lzero ℛ-conc

  module 𝔇 = CR 𝔇

  𝔇-cartesian : Cartesian-category 𝔇
  𝔇-cartesian = ConcPSh-cartesian ℛ-conc

  𝔇-closed : Cartesian-closed 𝔇 𝔇-cartesian
  𝔇-closed = ConcPSh-closed ℛ-conc

  open Cartesian-category 𝔇-cartesian
  open Cartesian-closed 𝔇-closed renaming ([_,_] to _⇒_)

  module 𝔇-ip {n} (F : Fin n → 𝔇.Ob) =
    Indexed-product (Cartesian→standard-finite-products terminal products F)

  □⟨_⟩ : Coeff → Functor 𝔇 𝔇
  □⟨ c ⟩ = F where
    F' : Functor (PSh lzero ℛ) (PSh lzero ℛ)
    F' = precompose (op μ⟨ c ⟩)

    F'-concrete
      : (A : ⌞ PSh lzero ℛ ⌟) → is-concrete ℛ-conc A
      → is-concrete ℛ-conc (F' .F₀ A)
    F'-concrete A conc {U = n , c'} {x} {y} H≡ = conc $ funext λ f →
      let α = path→iso {C = ℛ} (μ-pres-top {c})
          open FR A
      in  case μ-onto-points (f ℛ.∘ α .to) of λ g Hg p →
        A ⟪ f ⟫ x                           ≡⟨ expand (ℛ.insertr (α .inverses .invl)) $ₚ x ⟩
        A ⟪ α .from ⟫ (A ⟪ f ℛ.∘ α .to ⟫ x) ≡⟨ ap (A ⟪ _ ⟫_) (sym ⟨ p ⟩ $ₚ x ∙ H≡ $ₚ (g , Hg) ∙ ⟨ p ⟩ $ₚ y) ⟩
        A ⟪ α .from ⟫ (A ⟪ f ℛ.∘ α .to ⟫ y) ≡⟨ collapse (ℛ.cancelr (α .inverses .invl)) $ₚ y ⟩
        A ⟪ f ⟫ y                           ∎

    F : Functor 𝔇 𝔇
    F .F₀ (A , conc) = F' .F₀ A , F'-concrete A conc
    F .F₁ f          = full-hom (F' .F₁ (f .hom))
    F .F-id          = Subcat-hom-path (F' .F-id)
    F .F-∘ f g       = Subcat-hom-path (F' .F-∘ (f .hom) (g .hom))

  □-counit : □⟨ c ⟩ => Id
  □-counit .η X              = full-hom (nat-idr-op-to (X .fst ▸ opⁿ μ-unit))
  □-counit .is-natural _ _ f =
    Subcat-hom-path $ Nat-path λ _ → sym $ f .hom .is-natural _ _ _

  □-≤ : c ≤ c' → □⟨ c ⟩ => □⟨ c' ⟩
  □-≤ H≤ .η X                       = full-hom (X .fst ▸ opⁿ (μ-≤ H≤))
  □-≤ {c} {c'} H≤ .is-natural _ _ f =
    Subcat-hom-path $ Nat-path λ _ → sym $ f .hom .is-natural _ _ _

  □⟨A⟩-Id : □⟨ A↓ ⟩ ≅ⁿ Id
  □⟨A⟩-Id .to .η X = full-hom (nat-idr-op-to (X .fst ▸ opⁿ (μ⟨A⟩-Id .from)))
  □⟨A⟩-Id .to .is-natural _ _ f =
    Subcat-hom-path $ Nat-path λ _ → sym $ f .hom .is-natural _ _ _
  □⟨A⟩-Id .from .η X = full-hom (nat-idr-op-from (X .fst ▸ opⁿ (μ⟨A⟩-Id .to)))
  □⟨A⟩-Id .from .is-natural _ _ f =
    Subcat-hom-path $ Nat-path λ _ → sym $ f .hom .is-natural _ _ _
  □⟨A⟩-Id .inverses = record
    { invl = ext λ F _ _ → FR.annihilate (F .fst) (μ⟨A⟩-Id .inverses .invl ηₚ _) $ₚ _
    ; invr = ext λ F _ _ → FR.annihilate (F .fst) (μ⟨A⟩-Id .inverses .invr ηₚ _) $ₚ _
    }

  𝔇ℝ[_] : ℛ.Ob → 𝔇.Ob
  𝔇ℝ[_] = Conc-よ₀ ℛ-conc

  𝔇ℝ'[_] : Coeff ^ n → 𝔇.Ob
  𝔇ℝ'[ cs ] = 𝔇-ip.ΠF λ i → 𝔇ℝ[ 1 , cs i ]

  -- ⟨⟩-sec→section : {cs : Coeff ^ n} → ∫ₚ (⟨ cs ⟩-sec {m} c) → 𝔇ℝ'[ cs ] ʻ (m , c)
  -- ⟨⟩-sec→section {n = zero} (f , Hf)                  = lift tt
  -- ⟨⟩-sec→section {n = suc zero} {c = c} {cs} (f , Hf) = f , case Hf of λ Hf' →
  --   subst (_∈ ⟨ c ∣ cs fzero ⟩-reg) π'1 (Hf' fzero)
  -- ⟨⟩-sec→section {n = suc (suc n)} (f , Hf) =
  --   {!!} , {!!} -- (λ x → π'[ fzero ] f) , {!!}

  -- ⟨∥⟩-reg-morphism
  --   : {cs : Coeff ^ m} {cs' : Coeff ^ n} (f : ℝ ^ m → ℝ ^ n)
  --   → f ∈ ⟨ cs ∥ cs' ⟩-reg → Hom 𝔇ℝ'[ cs ] 𝔇ℝ'[ cs' ]
  -- ⟨∥⟩-reg-morphism {n = n} f Hf = {!!}
  -- -- full-hom record
  -- --   { η = λ U g → {!!} -- f ⊙ g
  -- --   ; is-natural = λ _ _ _ → {!!} }

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
  Sub-denot (sreal H≤)             = full-hom (よ₁ ℛ (ℛ-id≤ H≤))
  Sub-denot (stup {Ts' = Ts'} H<:) =
    𝔇-ip.tuple _ λ i → Sub-denot (H<: i) ∘ 𝔇-ip.π _ i
  Sub-denot (sarr {c = c} {e = det} {det} {T₁' = T₁'} {T₂' = T₂'} H<: H<:' H≤c H≤e) =
    □-≤ H≤c .η (⟦ T₁' ⟧ ⇒ ⟦ T₂' ⟧) ∘
    □⟨ c ⟩ .F₁ ([-,-]₁ _ _ 𝔇-closed (Sub-denot H<:') (Sub-denot H<:))
  Sub-denot (sarr {e' = rnd} H<: H<:' H≤c H≤e) = !
  Sub-denot (sdist H<:)                        = !

  -- -- env-≤-□ : Γ ≤ c → ⟦ Γ ⟧ ≅ⁿ □⟨ c ⟩ .F₀ ⟦ Γ ⟧
  -- -- env-≤-□ = ?

  -- -- ∩ᵗ-is-□ : ⟦ c ∩ᵗ T ⟧ ≡ □⟨ c ⟩ .F₀ ⟦ T ⟧
  -- -- ∩ᵗ-is-□ = {!!}

  -- Tm-denot : Γ ⊢ t :[ det ] T → Hom ⟦ Γ ⟧ ⟦ T ⟧
  -- Tm-denot (tsub {e = det} Hty _ H<:) = Sub-denot H<: ∘ Tm-denot Hty
  -- Tm-denot (tpromote {Γ = Γ} {Γ' = Γ'} Hty H≤ H⊆) =
  --   {!!} ∘ env-proj {Γ} {Γ'} H⊆
  -- Tm-denot {Γ} (tvar H∈) = π₂ {top} ∘ env-proj {Γ' = Γ} H∈
  -- Tm-denot (tlam {e = rnd} Hlam) = !
  -- Tm-denot {Γ} (tlam {T = T} {e = det} {T'} (Иi As Hty))
  --   with (a , H∉) ← fresh{𝔸} (As ∪ env-dom Γ) = □⟨A⟩-Id .from .η _ ∘ ƛ {⟦ T ⟧} body
  --   where
  --     body = subst (λ Γ → Hom ⟦ Γ ⟧ ⟦ T' ⟧) (env-nub-cons Γ (∉∪₂ As H∉))
  --       (Tm-denot (Hty a ⦃ ∉∪₁ H∉ ⦄))
  -- Tm-denot (tapp {T = T} {T' = T'} Hty Hty₁) =
  --   ev {⟦ T ⟧} ∘ ⟨ □-counit {A↓} .η (⟦ T ⟧ ⇒ ⟦ T' ⟧) ∘ Tm-denot Hty , Tm-denot Hty₁ ⟩
  -- Tm-denot (tprim {ϕ = ϕ} Hϕ Hty) =
  --   ⟨∥⟩-reg-morphism (Prim-denot ϕ) (Prim-reg Hϕ) ∘ Tm-denot Hty
  -- Tm-denot (treal {r = r}) =
  --   full-hom (よ₁ ℛ (ℛ-const (make r))) ∘ よ⋆-is-terminal ℛ-conc _ .centre ∘ !
  -- Tm-denot (ttup Htys) = 𝔇-ip.tuple _ λ i → Tm-denot (Htys i)
  -- Tm-denot (tproj i Hty) = 𝔇-ip.π _ i ∘ Tm-denot Hty
  -- Tm-denot (tif Hty Hty₁ Hty₂ H≤) = {!!}
  -- Tm-denot (tinfer Hty) = !
  -- Tm-denot (tdiff Hty Hty₁ Hc) = {!!}
  -- Tm-denot (tsolve Hty Hty₁ Hty₂ Hc) = {!!}
