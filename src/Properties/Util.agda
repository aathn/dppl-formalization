module Properties.Util where

-- Utility lemmas

open import Lib.Prelude
open import Lib.FunExt

open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.List using (_++_ ; map)
open import Data.List.Properties
  using (++-conicalʳ ; ∷-injective ; ∷-injectiveˡ ; ∷-injectiveʳ)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_ ; [] ; _∷_ ; _∷ʳ_)
import Data.Vec.Functional as V
open import Relation.Binary using (Rel ; Decidable)

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
  → --------------------------------------------------------
    (∀ i → A i) ⊎ ∃ λ j → B j × ∀ (i : Fin n) → i <ꟳ j → A i

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
  → {{x ∷ [] ≡ ys ++ y ∷ ys′}}
  → ----------------------------
    [] ≡ ys × x ≡ y × [] ≡ ys′

single-inv {ys = []} = refl , ∷-injective it
single-inv {ys = _ ∷ ys} with () ← ++-conicalʳ ys _ $ symm (∷-injectiveʳ it) 

map-∷-inv
  : ∀ {A B : Set} {Γ : List A} {Γ₁ : List B} {x : B} {f}
  → x ∷ Γ₁ ≡ map f Γ
  → -----------------
    ∃ λ y → ∃ λ Γ₁′ →
    y ∷ Γ₁′ ≡ Γ × x ≡ f y × Γ₁ ≡ map f Γ₁′

map-∷-inv {Γ = y ∷ Γ′} refl = y , Γ′ , refl , refl , refl

map-++-inv
  : ∀ {A B : Set} {Γ : List A} {Γ₁ Γ₂} {f : A → B}
  → Γ₁ ++ Γ₂ ≡ map f Γ
  → -------------------
    ∃ λ Γ₁′ → ∃ λ Γ₂′ →
    Γ₁′ ++ Γ₂′ ≡ Γ × Γ₁ ≡ map f Γ₁′ × Γ₂ ≡ map f Γ₂′

map-++-inv {Γ = Γ} {[]} Heq = [] , Γ , refl , refl , Heq
map-++-inv {Γ = x₁ ∷ Γ} {x ∷ Γ₁} Heq =
  let Γ₁′ , Γ₂′ , Heq₀ , Heq₁ , Heq₂ = map-++-inv {Γ = Γ} {Γ₁} (∷-injectiveʳ Heq)
  in  x₁ ∷ Γ₁′ , Γ₂′
    , ap (x₁ ∷_) Heq₀
    , ap₂ (_∷_) (∷-injectiveˡ Heq) Heq₁
    , Heq₂

vmap-injective
  : ∀ {n} {A B : Set} {xs ys : Vector A n}
  → (f : A → B)
  → (∀ {x y} → f x ≡ f y → x ≡ y)
  → ---------------------------------
    V.map f xs ≡ V.map f ys → xs ≡ ys

vmap-injective f f-inj Heq =
  funext λ i → f-inj $ ap (_$ i) Heq
