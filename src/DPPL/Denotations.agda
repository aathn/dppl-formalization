open import Lib.Algebra.Reals

module DPPL.Denotations (R : Reals₀) where

open Reals R using (ℝ ; 0r)

open import DPPL.Regularity hiding (A;P;C;M)
open import DPPL.Syntax R hiding (_▸_)
open import DPPL.Typing R
open import DPPL.Properties.Syntax R

open import Lib.Cat.Concrete
open import Lib.Cat.Functor
open import Lib.Cat.Product
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
open import Cat.Functor.Adjoint
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Base
open import Cat.Functor.Coherence
open import Cat.Functor.Hom
open import Cat.Functor.Naturality
open import Cat.Functor.Subcategory
open import Data.Dec.Base
open import Data.Fin.Base hiding (_≤_)
open import Data.List.Base
open import Data.Power hiding (_∪_ ; _∩_)
open import Order.Base
open import Order.Lattice
import Cat.Reasoning as Cr
import Cat.Functor.Reasoning as Fr

open SyntaxVars

open Reg↓≤ using (_≤_ ; ≤-refl ; ≤-trans)
open is-lattice Reg↓-lattice hiding (! ; top)

private
  ≤→is-yes : c ≤ c' → is-yes (holds? (c ≤ c'))
  ≤→is-yes = true→is-yes

  ≰→is-no : ¬ c ≤ c' → is-no (holds? (c ≤ c'))
  ≰→is-no = false→is-no

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
  open Cr._≅_
  open Cr.Inverses

  ⟨∣⟩-reg-≤ : c ≤ c' → ⟨ c ∣ c' ⟩-reg {m} {n} ≡ ⟨ c ⟩-reg
  ⟨∣⟩-reg-≤ {c = c} {c'} H≤ = ifᵈ-yes _ (≤→is-yes H≤)

  ⟨∣⟩-reg-≰ : ¬ c ≤ c' → ⟨ c ∣ c' ⟩-reg {m} {n} ≡ is-const
  ⟨∣⟩-reg-≰ {c = c} {c'} H≰ = ifᵈ-no _ (≰→is-no H≰)

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

  module ℛ = Cr ℛ

  ℛ-hom-path : {x y : ℛ.Ob} {f g : ℛ.Hom x y} → f .fst ≡ g .fst → f ≡ g
  ℛ-hom-path p = p ,ₚ prop!

  ℛ-terminal : Terminal ℛ
  ℛ-terminal = record
    { top  = (0 , bot)
    ; has⊤ = λ (m , c) → contr
      ((λ _ ()) , const-reg' λ ())
      (λ (x , _) → ℛ-hom-path (ext λ _ ()))
    }

  module ℛ⊤ = Terminal ℛ-terminal

  ℛ-id≤ : c ≤ c' → ℛ.Hom (m , c) (m , c')
  ℛ-id≤ H≤ = (λ x → x) , id-reg' H≤

  ℛ-const : ℝ ^ m → ℛ.Hom ℛ⊤.top (m , c)
  ℛ-const x = (λ _ → x) , const-reg' x

  ℛ-conc : Conc-category ℛ
  ℛ-conc .Conc-category.terminal          = ℛ-terminal
  ℛ-conc .Conc-category.⋆-hom-faithful H≡ = ℛ-hom-path
    $ funext (λ z → ap fst (H≡ $ₚ ℛ-const z) $ₚ make 0r)

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
  ... | yes _   | yes _  | no  _ = ℛ-hom-path refl
  ... | yes x≤c | no y≰c | z≤?c
    with f-const ← subst (_ ∈_) (⟨∣⟩-reg-≰ λ y≤x → y≰c (≤-trans y≤x x≤c)) Hf | z≤?c
  ... | yes _ =
    case f-const of λ x Hf' → ℛ-hom-path $ funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _))
  ... | no  _ =
    case f-const of λ x Hf' → ℛ-hom-path $ funext (λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _))

  μ-unit : Id => μ⟨ c ⟩
  μ-unit {c} .η (m , x) with holds? (x ≤ c)
  ... | yes _ = ℛ.id
  ... | no  _ = ℛ⊤.!
  μ-unit {c} .is-natural (m , z) (n , y) (f , Hf) with holds? (z ≤ c) | holds? (y ≤ c)
  ... | _      | no  _   = ℛ-hom-path refl
  ... | yes _  | yes _   = ℛ-hom-path refl
  ... | no z≰c | yes y≤c =
    case f-const of λ x Hf' → ℛ-hom-path $ funext λ _ → Hf' $ₚ _ ∙ sym (Hf' $ₚ _)
    where f-const = subst (_ ∈_) (⟨∣⟩-reg-≰ λ z≤y → z≰c (≤-trans z≤y y≤c)) Hf

  μ-mult : μ⟨ c ⟩ F∘ μ⟨ c' ⟩ ≅ⁿ μ⟨ c' ∩ c ⟩
  μ-mult {c} {c'} = to-natural-iso ni where
    -- This proof is... A hundred case splits followed by id or refl :)
    ni : make-natural-iso (μ⟨ c ⟩ F∘ μ⟨ c' ⟩) μ⟨ c' ∩ c ⟩
    ni .make-natural-iso.eta (m , z) with holds? (z ≤ c' ∩ c)
    ... | yes z≤∩ with yes _ ← holds? (z ≤ c') | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤l)
                  with yes _ ← holds? (z ≤ c)  | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤r) =
           ℛ.id
    ... | no z≰∩ with holds? (z ≤ c')
    ... | yes z≤c' with no _ ← holds? (z ≤ c)
      | _ ← ≰→is-no (λ z≤c → z≰∩ (∩-universal _ z≤c' z≤c))          = ℛ.id
    ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ.id
    ni .make-natural-iso.inv (m , z) with holds? (z ≤ c' ∩ c)
    ... | yes z≤∩ with yes _ ← holds? (z ≤ c') | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤l)
                  with yes _ ← holds? (z ≤ c)  | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤r) =
           ℛ.id
    ... | no z≰∩ with holds? (z ≤ c')
    ... | yes z≤c' with no _ ← holds? (z ≤ c)
      | _ ← ≰→is-no (λ z≤c → z≰∩ (∩-universal _ z≤c' z≤c))          = ℛ.id
    ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ.id
    ni .make-natural-iso.eta∘inv (m , z) with holds? (z ≤ c' ∩ c)
    ... | yes z≤∩ with yes _ ← holds? (z ≤ c') | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤l)
                  with yes _ ← holds? (z ≤ c)  | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤r) =
           ℛ-hom-path refl
    ... | no z≰∩ with holds? (z ≤ c')
    ... | yes z≤c' with no _ ← holds? (z ≤ c)
      | _ ← ≰→is-no (λ z≤c → z≰∩ (∩-universal _ z≤c' z≤c))          = ℛ-hom-path refl
    ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ-hom-path refl
    ni .make-natural-iso.inv∘eta (m , z) with holds? (z ≤ c' ∩ c)
    ... | yes z≤∩ with yes _ ← holds? (z ≤ c') | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤l)
                  with yes _ ← holds? (z ≤ c)  | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤r) =
           ℛ-hom-path refl
    ... | no z≰∩ with holds? (z ≤ c')
    ... | yes z≤c' with no _ ← holds? (z ≤ c)
      | _ ← ≰→is-no (λ z≤c → z≰∩ (∩-universal _ z≤c' z≤c))          = ℛ-hom-path refl
    ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ-hom-path refl
    ni .make-natural-iso.natural (m , z) _ _ with holds? (z ≤ c' ∩ c)
    ni .make-natural-iso.natural (m , z) _ _ | no z≰∩ with holds? (z ≤ c')
    ni .make-natural-iso.natural (m , z) (n , y) _ | no z≰∩ | yes z≤c'
      with no _ ← holds? (z ≤ c) | _ ← ≰→is-no (λ z≤c → z≰∩ (∩-universal _ z≤c' z≤c))
      with holds? (y ≤ c' ∩ c)
    ... | yes y≤∩ with yes _ ← holds? (y ≤ c') | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤l)
                  with yes _ ← holds? (y ≤ c)  | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤r) =
      ℛ-hom-path refl
    ... | no y≰∩ with holds? (y ≤ c')
    ... | yes y≤c' with no _ ← holds? (y ≤ c)
      | _ ← ≰→is-no (λ y≤c → y≰∩ (∩-universal _ y≤c' y≤c))          = ℛ-hom-path refl
    ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ-hom-path refl
    ni .make-natural-iso.natural (m , z) (n , y) _ | no z≰∩ | no _
      with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c})
      with holds? (y ≤ c' ∩ c)
    ... | yes y≤∩ with yes _ ← holds? (y ≤ c') | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤l)
                  with yes _ ← holds? (y ≤ c)  | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤r) =
      ℛ-hom-path refl
    ... | no y≰∩ with holds? (y ≤ c')
    ... | yes y≤c' with no _ ← holds? (y ≤ c)
      | _ ← ≰→is-no (λ y≤c → y≰∩ (∩-universal _ y≤c' y≤c))          = ℛ-hom-path refl
    ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ-hom-path refl
    ni .make-natural-iso.natural (m , z) (n , y) _ | yes z≤∩
      with yes _ ← holds? (z ≤ c') | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤l)
      with yes _ ← holds? (z ≤ c)  | _ ← ≤→is-yes (≤-trans z≤∩ ∩≤r)
      with holds? (y ≤ c' ∩ c)
    ... | yes y≤∩ with yes _ ← holds? (y ≤ c') | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤l)
                  with yes _ ← holds? (y ≤ c)  | _ ← ≤→is-yes (≤-trans y≤∩ ∩≤r) =
      ℛ-hom-path refl
    ... | no y≰∩ with holds? (y ≤ c')
    ... | yes y≤c' with no _ ← holds? (y ≤ c)
      | _ ← ≰→is-no (λ y≤c → y≰∩ (∩-universal _ y≤c' y≤c))          = ℛ-hom-path refl
    ... | no _ with yes _ ← holds? (bot ≤ c) | _ ← ≤→is-yes (¡ {c}) = ℛ-hom-path refl

  μ-≤ : c' ≤ c → μ⟨ c ⟩ => μ⟨ c' ⟩
  μ-≤ {c'} {c} H≤ .η (m , x) with holds? (x ≤ c)
  ... | yes _ = μ-unit .η (m , x)
  ... | no x≰c
    with no _ ← holds? (x ≤ c') | _ ← ≰→is-no (λ x≤c' → x≰c (≤-trans x≤c' H≤)) = ℛ⊤.!
  μ-≤ {c'} {c} H≤ .is-natural (m , z) (n , y) (f , Hf)
    with holds? (z ≤ c) | holds? (y ≤ c)
  ... | yes _    | yes _ = μ-unit .is-natural _ _ (f , Hf)
  ... | no z≰c   | yes _ with no _ ← holds? (z ≤ c')
    | _ ← ≰→is-no (λ z≤c' → z≰c (≤-trans z≤c' H≤)) | holds? (y ≤ c')
  ... | no _  = ℛ⊤.!-unique₂ _ _
  ... | yes _ = ℛ.idl _ ∙ ℛ.intror (ℛ⊤.!-unique _)
  μ-≤ {c'} {c} H≤ .is-natural _ (n , y) _ | _ | no y≰c
    with no _ ← holds? (y ≤ c') | _ ← ≰→is-no (λ y≤c' → y≰c (≤-trans y≤c' H≤)) =
    ℛ⊤.!-unique₂ _ _

  μ⟨A⟩-Id : μ⟨ A↓ ⟩ ≅ⁿ Id
  μ⟨A⟩-Id = to-natural-iso ni where
    ni : make-natural-iso μ⟨ A↓ ⟩ Id
    ni .make-natural-iso.eta (m , c)
      with yes _ ← holds? (c ≤ A↓) | _ ← ≤→is-yes {c} A! = ℛ.id
    ni .make-natural-iso.inv (m , c)
      with yes _ ← holds? (c ≤ A↓) | _ ← ≤→is-yes {c} A! = ℛ.id
    ni .make-natural-iso.eta∘inv (m , c)
      with yes _ ← holds? (c ≤ A↓) | _ ← ≤→is-yes {c} A! = ℛ.idl _
    ni .make-natural-iso.inv∘eta (m , c)
      with yes _ ← holds? (c ≤ A↓) | _ ← ≤→is-yes {c} A! = ℛ.idl _
    ni .make-natural-iso.natural (m , c) (n , c') f
      with yes _ ← holds? (c ≤ A↓)  | _ ← ≤→is-yes {c} A!
         | yes _ ← holds? (c' ≤ A↓) | _ ← ≤→is-yes {c'} A! =
      ℛ.id-comm

  μ-pres-top : μ⟨ c ⟩ .F₀ ℛ⊤.top ≡ ℛ⊤.top
  μ-pres-top {c = c} = ifᵈ-yes (holds? (bot ≤ c)) (≤→is-yes ¡)

  μ-onto-points : ∀ {U} → is-surjective (μ⟨ c ⟩ .F₁ {ℛ⊤.top} {U})
  μ-onto-points {c = c} {n , c'} (f , Hf) with holds? (c' ≤ c)
  ... | no  _ = inc (ℛ-const (make 0r) , ℛ⊤.!-unique _)
  ... | yes _ with yes _ ← holds? (bot ≤ c)  | _ ← ≤→is-yes (¡ {c})
              with yes _ ← holds? (bot ≤ c') | _ ← ≤→is-yes (¡ {c'}) =
    inc ((f , Hf) , refl)

  ν⟨_⟩ : Coeff → Functor ℛ ℛ
  ν⟨ c ⟩ .F₀ (n , x)                  = n , c ∩ x
  ν⟨ c ⟩ .F₁ {m , z} {n , y} (f , Hf) = f , Hf' where
    Hf' : f ∈ ⟨ c ∩ z ∣ c ∩ y ⟩-reg
    Hf' with holds? (z ≤ y)
    ... | yes z≤y = subst (_ ∈_) (sym $ ⟨∣⟩-reg-≤ (∩≤∩r z≤y)) (⊆-reg ∩≤r _ Hf)
    ... | no _    = case Hf of λ x p → subst (_∈ ⟨ _ ∣ _ ⟩-reg) (sym p) (const-reg' x)
  ν⟨ c ⟩ .F-id    = ℛ-hom-path refl
  ν⟨ c ⟩ .F-∘ _ _ = ℛ-hom-path refl

  ν-counit : ν⟨ c ⟩ => Id
  ν-counit .η X              = ℛ-id≤ ∩≤r
  ν-counit .is-natural _ _ f = ℛ-hom-path refl

  ν-pres-top : ν⟨ c ⟩ .F₀ ℛ⊤.top ≡ ℛ⊤.top
  ν-pres-top {c = c} = refl ,ₚ ∩-comm ∙ order→∩ ¡

  ν-onto-points : ∀ {U} → is-surjective (ν⟨ c ⟩ .F₁ {ℛ⊤.top} {U})
  ν-onto-points {c = c} {n , c'} f =
    inc ( ν-counit .η _ ℛ.∘ f ℛ.∘ path→iso {C = ℛ} ν-pres-top .from
        , ℛ-hom-path (funext λ z → ap (f .fst) (transport-refl _ ∙ transport-refl z))
        )

  μ-dominates-ν : ν⟨ c ⟩ F∘ μ⟨ c ⟩ ≅ⁿ μ⟨ c ⟩
  μ-dominates-ν {c} = to-natural-iso ni where
    ni : make-natural-iso (ν⟨ c ⟩ F∘ μ⟨ c ⟩) μ⟨ c ⟩
    ni .make-natural-iso.eta _ = ν-counit .η _
    ni .make-natural-iso.inv (m , z) with holds? (z ≤ c)
    ... | yes z≤c = ℛ-id≤ (∩-universal _ z≤c ≤-refl)
    ... | no _    = ℛ-const (make 0r)
    ni .make-natural-iso.eta∘inv (m , z) with holds? (z ≤ c)
    ... | yes z≤c = ℛ-hom-path refl
    ... | no _    = ℛ-hom-path $ ext λ _ ()
    ni .make-natural-iso.inv∘eta (m , z) with holds? (z ≤ c)
    ... | yes z≤c = ℛ-hom-path refl
    ... | no _    = ℛ-hom-path $ ext λ _ ()
    ni .make-natural-iso.natural _ _ _ = ℛ-hom-path refl

  ν-dominates-μ : μ⟨ c ⟩ F∘ ν⟨ c ⟩ ≅ⁿ ν⟨ c ⟩
  ν-dominates-μ {c} = to-natural-iso ni where
    ni : make-natural-iso (μ⟨ c ⟩ F∘ ν⟨ c ⟩) ν⟨ c ⟩
    ni .make-natural-iso.eta (m , z)
      with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) = ℛ.id
    ni .make-natural-iso.inv (m , z)
      with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) = ℛ.id
    ni .make-natural-iso.eta∘inv (m , z)
      with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) = ℛ-hom-path refl
    ni .make-natural-iso.inv∘eta (m , z)
      with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) = ℛ-hom-path refl
    ni .make-natural-iso.natural (m , z) (n , y) _
      with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z})
         | yes _ ← holds? (c ∩ y ≤ c) | _ ← ≤→is-yes (∩≤l {c} {y}) = ℛ-hom-path refl

  μ⊣ν : μ⟨ c ⟩ ⊣ ν⟨ c ⟩
  μ⊣ν {c} ._⊣_.unit   = μ-dominates-ν .from ∘nt μ-unit {c}
  μ⊣ν {c} ._⊣_.counit = ν-counit {c} ∘nt ν-dominates-μ .to
  μ⊣ν {c} ._⊣_.zig {m , z} with holds? (z ≤ c)
  ... | yes _ with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) =
    ℛ-hom-path refl
  ... | no _ with yes _ ← holds? (c ∩ bot ≤ c) | _ ← ≤→is-yes (∩≤l {c} {bot}) =
    ℛ-hom-path $ ext λ _ ()
  μ⊣ν {c} ._⊣_.zag {m , z}
    with yes _ ← holds? (c ∩ z ≤ c) | _ ← ≤→is-yes (∩≤l {c} {z}) = ℛ-hom-path refl

  𝔇 : Precategory _ _
  𝔇 = ConcPSh lzero ℛ-conc

  module 𝔇 = Cr 𝔇

  𝔇-cartesian : Cartesian-category 𝔇
  𝔇-cartesian = ConcPSh-cartesian ℛ-conc

  𝔇-closed : Cartesian-closed 𝔇 𝔇-cartesian
  𝔇-closed = ConcPSh-closed ℛ-conc

  open Cartesian-category 𝔇-cartesian
  open Cartesian-closed 𝔇-closed renaming ([_,_] to _⇒_)

  module 𝔇-ip {n} (F : Fin n → 𝔇.Ob) =
    Indexed-product (Cartesian→standard-finite-products terminal products F)
  open ProdIso 𝔇-cartesian

  □⟨_⟩ : Coeff → Functor 𝔇 𝔇
  □⟨ c ⟩ = conc-dir-image ℛ-conc ℛ-conc μ⟨ c ⟩ (path→iso μ-pres-top) μ-onto-points

  -- □-counit : □⟨ c ⟩ => Id
  -- □-counit = sub-nat λ where
  --   .η X              → nat-idr-op-to (X .fst ▸ opⁿ μ-unit)
  --   .is-natural _ _ f → Nat-path λ _ → sym $ f .hom .is-natural _ _ _

  -- □-comult : □⟨ c ⟩ F∘ □⟨ c' ⟩ ≅ⁿ □⟨ c ∩ c' ⟩
  -- □-comult .to = sub-nat λ where
  --   .η X              → nat-assoc-from (X .fst ▸ op-compose-from (opⁿ (μ-mult .from)))
  --   .is-natural _ _ f → Nat-path λ _ → sym $ f .hom .is-natural _ _ _
  -- □-comult .from = sub-nat λ where
  --   .η X              → nat-assoc-to (X .fst ▸ op-compose-into (opⁿ (μ-mult .to)))
  --   .is-natural _ _ f → Nat-path λ _ → sym $ f .hom .is-natural _ _ _
  -- □-comult .inverses = λ where
  --   .invl → ext λ F _ _ → Fr.annihilate (F .fst) (μ-mult .inverses .invl ηₚ _) $ₚ _
  --   .invr → ext λ F _ _ → Fr.annihilate (F .fst) (μ-mult .inverses .invr ηₚ _) $ₚ _

  -- □-≤ : c ≤ c' → □⟨ c ⟩ => □⟨ c' ⟩
  -- □-≤ {c} {c'} H≤ = sub-nat λ where
  --   .η X              → X .fst ▸ opⁿ (μ-≤ H≤)
  --   .is-natural _ _ f → Nat-path λ _ → sym $ f .hom .is-natural _ _ _

  -- □⟨A⟩-Id : □⟨ A↓ ⟩ ≅ⁿ Id
  -- □⟨A⟩-Id .to = sub-nat λ where
  --   .η X              → nat-idr-op-to (X .fst ▸ opⁿ (μ⟨A⟩-Id .from))
  --   .is-natural _ _ f → Nat-path λ _ → sym $ f .hom .is-natural _ _ _
  -- □⟨A⟩-Id .from = sub-nat λ where
  --   .η X              → nat-idr-op-from (X .fst ▸ opⁿ (μ⟨A⟩-Id .to))
  --   .is-natural _ _ f → Nat-path λ _ → sym $ f .hom .is-natural _ _ _
  -- □⟨A⟩-Id .inverses = λ where
  --   .invl → ext λ F _ _ → Fr.annihilate (F .fst) (μ⟨A⟩-Id .inverses .invl ηₚ _) $ₚ _
  --   .invr → ext λ F _ _ → Fr.annihilate (F .fst) (μ⟨A⟩-Id .inverses .invr ηₚ _) $ₚ _

  ◇⟨_⟩ : Coeff → Functor 𝔇 𝔇
  ◇⟨ c ⟩ = conc-dir-image ℛ-conc ℛ-conc ν⟨ c ⟩ (path→iso ν-pres-top) ν-onto-points

  ◇⊣□ : ◇⟨ c ⟩ ⊣ □⟨ c ⟩
  ◇⊣□ {c} = {!!} where
    foo : precompose (op μ⟨ c ⟩) {D = Sets lzero} ⊣ precompose (op ν⟨ c ⟩)
    foo = precomposite-adjunction (opposite-adjunction μ⊣ν)


  -- □-pres-top : □⟨ c ⟩ .F₀ top ≅ top
  -- □-pres-top = {!!}

  -- □-pres-prod : ∀ X Y → □⟨ c ⟩ .F₀ (X ⊗₀ Y) ≅ (□⟨ c ⟩ .F₀ X ⊗₀ □⟨ c ⟩ .F₀ Y)
  -- □-pres-prod = {!!}

  -- □-pres-ip
  --   : ∀ (F : Fin n → 𝔇.Ob) → □⟨ c ⟩ .F₀ (𝔇-ip.ΠF F) ≅ 𝔇-ip.ΠF λ i → □⟨ c ⟩ .F₀ (F i)
  -- □-pres-ip {n = zero} F                = □-pres-top
  -- □-pres-ip {n = suc zero} F            = id-iso
  -- □-pres-ip {n = suc (suc n)} {c = c} F = □-pres-prod (F fzero) (𝔇-ip.ΠF (F ⊙ fsuc))
  --   ∙Iso (id-iso {□⟨ c ⟩ .F₀ (F fzero)} ⊗Iso □-pres-ip (F ⊙ fsuc))

  -- 𝔇ℝ[_] : ℛ.Ob → 𝔇.Ob
  -- 𝔇ℝ[_] = Conc-よ₀ ℛ-conc

  -- 𝔇ℝ'[_] : Coeff ^ n → 𝔇.Ob
  -- 𝔇ℝ'[ cs ] = 𝔇-ip.ΠF λ i → 𝔇ℝ[ 1 , cs i ]

  -- -- ⟨⟩-sec→section : {cs : Coeff ^ n} → ∫ₚ (⟨ cs ⟩-sec {m} c) → 𝔇ℝ'[ cs ] ʻ (m , c)
  -- -- ⟨⟩-sec→section {n = zero} (f , Hf)                  = lift tt
  -- -- ⟨⟩-sec→section {n = suc zero} {c = c} {cs} (f , Hf) = f , case Hf of λ Hf' →
  -- --   subst (_∈ ⟨ c ∣ cs fzero ⟩-reg) π'1 (Hf' fzero)
  -- -- ⟨⟩-sec→section {n = suc (suc n)} (f , Hf) =
  -- --   {!!} , {!!} -- (λ x → π'[ fzero ] f) , {!!}

  -- -- ⟨∥⟩-reg-morphism
  -- --   : {cs : Coeff ^ m} {cs' : Coeff ^ n} (f : ℝ ^ m → ℝ ^ n)
  -- --   → f ∈ ⟨ cs ∥ cs' ⟩-reg → Hom 𝔇ℝ'[ cs ] 𝔇ℝ'[ cs' ]
  -- -- ⟨∥⟩-reg-morphism {n = n} f Hf = {!!}
  -- -- -- full-hom record
  -- -- --   { η = λ U g → {!!} -- f ⊙ g
  -- -- --   ; is-natural = λ _ _ _ → {!!} }

  -- Ty-denot : Ty → 𝔇.Ob
  -- Ty-denot (treal c)            = 𝔇ℝ[ 1 , c ]
  -- Ty-denot (T₁ ⇒[ c , det ] T₂) = □⟨ c ⟩ .F₀ (Ty-denot T₁ ⇒ Ty-denot T₂)
  -- Ty-denot (ttup n Ts)          = 𝔇-ip.ΠF λ i → Ty-denot (Ts i)
  -- -- Distributions are interpreted trivially for the time being.
  -- Ty-denot (tdist _)          = top
  -- Ty-denot (_ ⇒[ _ , rnd ] _) = top

  -- instance
  --   ⟦⟧-Ty : ⟦⟧-notation Ty
  --   ⟦⟧-Ty = brackets _ Ty-denot

  -- open EnvDenot 𝔇-cartesian Ty-denot
  -- open TypingVars
  -- open FinsetSyntax

  -- Sub-denot : T <: T' → Hom ⟦ T ⟧ ⟦ T' ⟧
  -- Sub-denot (sreal H≤)             = full-hom (よ₁ ℛ (ℛ-id≤ H≤))
  -- Sub-denot (stup {Ts' = Ts'} H<:) =
  --   𝔇-ip.tuple _ λ i → Sub-denot (H<: i) ∘ 𝔇-ip.π _ i
  -- Sub-denot (sarr {c = c} {e = det} {det} {T₁' = T₁'} {T₂' = T₂'} H<: H<:' H≤c H≤e) =
  --   □-≤ H≤c .η (⟦ T₁' ⟧ ⇒ ⟦ T₂' ⟧) ∘
  --   □⟨ c ⟩ .F₁ ([-,-]₁ _ _ 𝔇-closed (Sub-denot H<:') (Sub-denot H<:))
  -- Sub-denot (sarr {e' = rnd} H<: H<:' H≤c H≤e) = !
  -- Sub-denot (sdist H<:)                        = !

  -- ∩ᵗ-is-□ : ∀ T → □⟨ c ⟩ .F₀ ⟦ T ⟧ ≅ ⟦ c ∩ᵗ T ⟧
  -- ∩ᵗ-is-□ (treal c')          = iso→sub-iso (adjunct-hom-iso-into μ⊣ν _)
  -- ∩ᵗ-is-□ (T ⇒[ _ , det ] T₁) = isoⁿ→iso □-comult (Ty-denot T ⇒ Ty-denot T₁)
  -- ∩ᵗ-is-□ (ttup n Ts)         =
  --   □-pres-ip (λ i → Ty-denot (Ts i)) ∙Iso ΠIso (λ i → ∩ᵗ-is-□ (Ts i))
  -- ∩ᵗ-is-□ (tdist _)           = □-pres-top
  -- ∩ᵗ-is-□ (_ ⇒[ _ , rnd ] _)  = □-pres-top

  -- raw-env-≤-□
  --   : {l : RawEnv Ty} → is-nubbed l → (∀ {x} → raw-sub (x ∷ []) l → x .snd ≤ᵗ c)
  --   → □⟨ c ⟩ .F₀ ⟦ l ⟧ ≅ ⟦ l ⟧
  -- raw-env-≤-□ [] H≤                                    = □-pres-top
  -- raw-env-≤-□ {c = c} {l = (a , T) ∷ l} (H∉ ∷ Hnub) H≤ =
  --   let p : c ∩ᵗ T ≡ T
  --       p = ≤ᵗ→∩ᵗ (H≤ (sub-cons reflᵢ H∉ sub-nil))
  --       Hl : □⟨ c ⟩ .F₀ (RawEnv-denot l) ≅ RawEnv-denot l
  --       Hl = raw-env-≤-□ Hnub λ H∈ → H≤ (sub-consr tt H∈)
  --       HT : □⟨ c ⟩ .F₀ (Ty-denot T) ≅ Ty-denot T
  --       HT = ∩ᵗ-is-□ T ∙Iso path→iso (ap Ty-denot p)
  --   in
  --   □-pres-prod (RawEnv-denot l) (Ty-denot T) ∙Iso (Hl ⊗Iso HT)

  -- env-≤-□ : Γ ≤ᵉ c → □⟨ c ⟩ .F₀ ⟦ Γ ⟧ ≅ ⟦ Γ ⟧
  -- env-≤-□ {Γ = Γ} H≤ = raw-env-≤-□ (env-nub-is-nubbed Γ) (H≤ ⊙ env-mem-nub)

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
