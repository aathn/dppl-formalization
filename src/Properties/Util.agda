module Properties.Util where

-- Lemmas regarding substitution and other utility lemmas

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.LocalClosedness
open import Lib.Freshness
open import Lib.oc-Sets
open import Lib.FunExt
open import Lib.BindingSignature

open import Function using (_$_)
open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.Product using (∃-syntax)
open import Data.List using (_++_ ; map)
open import Data.List.Properties
  using (++-conicalʳ ; ∷-injective ; ∷-injectiveˡ ; ∷-injectiveʳ)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_ ; [] ; _∷ʳ_)
import Data.Vec.Functional as V

module _ {Σ : Sig} where
  open Subst {Σ}

  subst-open-comm
    : ∀ {x y n u} t
    → x ≠ y
    → 0 ≻ u
    → -----------------------------------------
      (x => u)((n ~> y)t) ≡ (n ~> y)((x => u)t)
  subst-open-comm {x} {y} {n} (bvar x₁) Hneq Hlc with n ≐ x₁
  ... | neq _ = refl
  ... | equ rewrite Hneq = refl
  subst-open-comm {x} {y} {n} (fvar y₁) Hneq Hlc with x ≐ y₁
  ... | neq _ = refl
  ... | equ rewrite ≻3 {j = n} {y} Hlc 0≤ = refl
  subst-open-comm (op (o , ts)) Hneq Hlc =
    ap (op ∘ (o ,_)) $ funext λ i → subst-open-comm (ts i) Hneq Hlc

  subst-intro
    : ∀ {x n u} t
    → x ∉ fv t
    → -------------------------------
      (n ≈> u)t ≡ (x => u)((n ~> x)t)
  subst-intro {x} {n} (bvar x₁) H∉ with n ≐ x₁
  ... | neq _ = refl
  ... | equ rewrite dec-equ x = refl
  subst-intro {x} (fvar y) H∉ with x ≐ y | H∉
  ... | neq _ | _   = refl
  ... | equ   | ∉[] with () ← ¬≠ x it
  subst-intro {x} {n} {u} (op (o , ts)) H∉ =
    ap (op ∘ (o ,_)) $ funext λ i → subst-intro (ts i) (∉⋃ _ i {{H∉}})

  subst-fresh
    : ∀ {x} u t
    → x ∉ fv t
    → --------------
      (x => u) t ≡ t
  subst-fresh u (bvar x) H∉ = refl
  subst-fresh u (fvar y) (∉[] {{p}}) rewrite p = refl
  subst-fresh u (op (o , ts)) H∉ =
    ap (op ∘ (o ,_)) $ funext λ i → subst-fresh u (ts i) (∉⋃ _ i {{H∉}})

  open-notin
    : ∀ {x y n} t
    → x ∉ fv {Σ} ((n ~> y) t)
    → x ∉ fv t
  open-notin (bvar x) H∉ = ∉Ø
  open-notin (fvar y) H∉ = H∉
  open-notin (op (o , ts)) H∉ =
    ∉⋃′ (fv ∘ ts) λ i → open-notin (ts i) (∉⋃ _ i {{H∉}})

_∈?_ : {A : Set} {{_ : hasDecEq A}} → (x : A) (xs : Fset A) → Dec (x ∈ xs)
x ∈? Ø = no ∉→¬∈
x ∈? [ x₁ ] with x ≐ x₁
... | equ    = yes ∈[]
... | neq ¬a = no λ { ∈[] → ¬a refl }
x ∈? (xs ∪ xs₁) with x ∈? xs
... | yes p = yes (∈∪₁ p)
... | no ¬a with x ∈? xs₁
...   | yes p = yes (∈∪₂ p)
...   | no ¬b = no λ { (∈∪₁ p) → ¬a p ; (∈∪₂ q) → ¬b q }

all-⊎
  : ∀ {n} {A B : Fin n → Set}
  → (∀ i → A i ⊎ B i)
  → -------------------------------------------------------
    (∀ i → A i) ⊎ ∃[ j ] B j × ∀ (i : Fin n) → i <ꟳ j → A i

all-⊎ {zero} f = ι₁ λ()
all-⊎ {n +1} f =
  case (f zero) λ
    { (ι₁ Ha) →
      case (all-⊎ (f ∘ succ)) λ
        { (ι₁ Has) → ι₁ $ λ { zero → Ha ; (succ n) → Has n }
        ; (ι₂ (j , Hb , Has)) → ι₂ $
          _ , Hb , λ { zero _ → Ha ; (succ n) H≤ → Has n (≤-1 H≤) }
        }
    ; (ι₂ Hb) → ι₂ $ _ , Hb , λ _ ()
    }

single-inv
  : ∀ {A : Set} {x y : A} {ys ys′}
  → {{x :: [] ≡ ys ++ y :: ys′}}
  → ----------------------------
    [] ≡ ys × x ≡ y × [] ≡ ys′

single-inv {ys = []} = refl , ∷-injective it
single-inv {ys = _ :: ys} with () ← ++-conicalʳ ys _ $ symm (∷-injectiveʳ it) 

map-::-inv
  : ∀ {A B : Set} {Γ : List A} {Γ₁ : List B} {x : B} {f}
  → x :: Γ₁ ≡ map f Γ
  → -----------------
    ∃[ y ] ∃[ Γ₁′ ]
    y :: Γ₁′ ≡ Γ × x ≡ f y × Γ₁ ≡ map f Γ₁′

map-::-inv {Γ = y :: Γ′} refl = y , Γ′ , refl , refl , refl

map-++-inv
  : ∀ {A B : Set} {Γ : List A} {Γ₁ Γ₂} {f : A → B}
  → Γ₁ ++ Γ₂ ≡ map f Γ
  → ------------------
    ∃[ Γ₁′ ] ∃[ Γ₂′ ]
    Γ₁′ ++ Γ₂′ ≡ Γ × Γ₁ ≡ map f Γ₁′ × Γ₂ ≡ map f Γ₂′

map-++-inv {Γ = Γ} {[]} Heq = [] , Γ , refl , refl , Heq
map-++-inv {Γ = x₁ :: Γ} {x :: Γ₁} Heq =
  let Γ₁′ , Γ₂′ , Heq₀ , Heq₁ , Heq₂ = map-++-inv {Γ = Γ} {Γ₁} (∷-injectiveʳ Heq)
  in  x₁ :: Γ₁′ , Γ₂′
    , ap (x₁ ::_) Heq₀
    , ap₂ (_::_) (∷-injectiveˡ Heq) Heq₁
    , Heq₂

vmap-injective
  : ∀ {n} {A B : Set} {xs ys : Vector A n}
  → (f : A → B)
  → (∀ {x y} → f x ≡ f y → x ≡ y)
  → ---------------------------------
    V.map f xs ≡ V.map f ys → xs ≡ ys

vmap-injective f f-inj Heq =
  funext λ i → f-inj $ ap (_$ i) Heq

[]-⊆
  : ∀ {A : Set} {l : List A}
  → ------
    [] ⊆ l

[]-⊆ {l = []} = []
[]-⊆ {l = x :: l} = x ∷ʳ []-⊆
