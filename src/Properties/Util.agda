module Properties.Util where


-- Utility lemmas
open import Lib.Prelude
open import Lib.FunExt

open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.List using (_++_ ; map)
open import Data.List.Properties
  using (++-conicalʳ ; ∷-injective ; ∷-injectiveˡ ; ∷-injectiveʳ)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_ ; [] ; _∷ʳ_)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
import Data.Vec.Functional as V

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

all-⊎ :
  {n : ℕ}
  {A B : Fin n → Set}
  (_ : ∀ i → A i ⊎ B i)
  → ------------------------------------------------------
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

single-inv :
  {A : Set}
  {x y : A}
  {ys ys′ : List A}
  {{_ : x ∷ [] ≡ ys ++ y ∷ ys′}}
  → ----------------------------
  [] ≡ ys × x ≡ y × [] ≡ ys′

single-inv {ys = []} = refl , ∷-injective it
single-inv {ys = _ ∷ ys} with () ← ++-conicalʳ ys _ $ symm (∷-injectiveʳ it) 

vmap-injective :
  {n : ℕ}
  {A B : Set}
  (f : A → B)
  → ---------------------------------------------------
  injection _≡_ _≡_ f → injection _≡_ _≡_ (V.map f {n})

vmap-injective f f-inj Heq =
  funext λ i → f-inj $ ap (_$ i) Heq

all-weaken :
  {A : Set}
  {P : A → Set}
  {l₁ l₂ : List A}
  {x : A}
  → -------------------------------------
  All P (l₁ ++ x ∷ l₂) → All P (l₁ ++ l₂)
all-weaken {l₁ = []} (px ∷ Hall) = Hall
all-weaken {l₁ = x ∷ l₁} (px ∷ Hall) = px ∷ all-weaken Hall
