module Lib.Finset where

open import 1Lab.Prelude hiding (_≠_ ; _∉_)

open import Lib.Dec
open import Data.Finset.Base

open import Order.Base using (Poset)
open import Order.Diagram.Join using (Join)
open import Order.Instances.Nat using (Nat-poset; Nat-joins; Nat-bottom)
open import Order.Semilattice.Join using (is-join-semilattice)
open import Data.Dec.Base using (Discrete)
open import Data.Nat.Base using (max)
open import Data.Nat.Order using (¬sucx≤x)
open import Data.Sum.Base using (_⊎_ ; inr ; inl)
open import Data.Sum.Properties using (Discrete-⊎)
open import Data.Finset.Properties using (map-∈ᶠˢ ; unionl-∈ᶠˢ ; unionr-∈ᶠˢ ; ∈ᶠˢ-union ; filter-∈ᶠˢ)

private variable
  ℓ : Level
  A B : Type ℓ

∷≠[] : ∀ {x : A} {xs} → ¬ x ∷ xs ≡ []
∷≠[] {A = A} p = subst (λ x → ∣ distinguish x ∣) p tt where
  distinguish : Finset A → Prop lzero
  distinguish [] = el ⊥ (hlevel 1)
  distinguish (x ∷ xs) = el ⊤ (hlevel 1)
  distinguish (∷-dup x xs i) = el ⊤ (hlevel 1)
  distinguish (∷-swap x y xs i) = el ⊤ (hlevel 1)
  distinguish (squash x y p q i j) =
    n-Type-is-hlevel 1
      (distinguish x) (distinguish y)
      (λ i → distinguish (p i)) (λ i → distinguish (q i)) i j

module _ {o ℓ : Level} {P : Poset o ℓ} ⦃ joins : is-join-semilattice P ⦄ where
  open Poset P
  open is-join-semilattice joins

  fold : Finset ⌞ P ⌟ → ⌞ P ⌟
  fold [] = bot
  fold (x ∷ xs) = x ∪ fold xs
  fold (∷-dup x xs i) =
    (∪-assoc {x} ∙ ap (_∪ fold xs) ∪-idem) i
  fold (∷-swap x y xs i) =
    (∪-assoc {x} {y} ∙ ap (_∪ fold xs) ∪-comm ∙ sym ∪-assoc) i
  fold (squash x y p q i j) =
    Poset.Ob-is-set P _ _ (λ k → fold (p k)) (λ k → fold (q k)) i j

  ≤fold : ∀{x xs} → x ∈ xs → x ≤ fold xs
  ≤fold {x} {xs} H∈ =
    ∈ᶠˢ-elim (λ xs _ → x ≤ fold xs)
      (λ {_} → l≤∪)
      (λ q z → ≤-trans z r≤∪)
      xs H∈

private instance
  Nat-is-join-semilattice : is-join-semilattice Nat-poset
  Nat-is-join-semilattice = record
    { _∪_ = max
    ; ∪-joins = λ x y → Join.has-join (Nat-joins x y)
    ; has-bottom = Nat-bottom
    }

-- Maximum of a finite set of numbers
maxfs : Finset Nat → Nat
maxfs = fold

maxfs+1∉ : (xs : Finset Nat) → suc (maxfs xs) ∉ xs
maxfs+1∉ xs = ¬∈→∉ {ℙA = Finset Nat} λ H∈ → ¬sucx≤x _ (≤fold H∈)

-- Subtract an element
infix 6 _-[_]
_-[_] :
  ⦃ _ : Discrete A ⦄
  (xs : Finset A)
  (x : A)
  → ----------------
  Finset A
xs -[ x ] = filter (¬_ ∘ (_≡ x)) xs

inr⁻¹ : Finset (A ⊎ B) → Finset B
inr⁻¹ = _>>= λ
  { (inl _) → []
  ; (inr y) → y ∷ []
  }

thereₛ-inr⁻¹
  : {y : B} {y' : A ⊎ B} {xs : Finset (A ⊎ B)}
  → y ∈ᶠˢ inr⁻¹ xs → y ∈ᶠˢ inr⁻¹ (y' ∷ xs)
thereₛ-inr⁻¹ {y' = inl x} H∈ = H∈
thereₛ-inr⁻¹ {y' = inr x} H∈ = thereₛ H∈

∉inr⁻¹→inr∉ :
  ⦃ _ : Discrete A ⦄
  ⦃ _ : Discrete B ⦄
  (zs : Finset (A ⊎ B))
  (y : B)
  → -----------------------
  y ∉ inr⁻¹ zs → inr y ∉ zs
∉inr⁻¹→inr∉ {A = A} {B = B} zs y H∉ =
  ¬∈→∉ {ℙA = Finset (A ⊎ B)} λ H∈ → ∉→¬∈ {ℙA = Finset B} H∉ $
  ∈ᶠˢ-elim (λ zs _ → y ∈ inr⁻¹ zs)
    hereₛ
    (λ {y' xs} _ → thereₛ-inr⁻¹ {y' = y'} {xs})
    zs H∈

∉∷₁ :
  ⦃ _ : Discrete A ⦄
  {x y : A}
  {ys : Finset A}
  ⦃ H∉ : x ∉ (y ∷ ys) ⦄
  → ------------------
  x ≠ y
∉∷₁ {A = A} = ¬≡→≠ λ H≡ → ∉→¬∈ {ℙA = Finset A} auto (hereₛ' (Id≃path.from H≡))

∉∷₂ :
  ⦃ _ : Discrete A ⦄
  {x y : A}
  {ys : Finset A}
  ⦃ H∉ : x ∉ (y ∷ ys) ⦄
  → ------------------
  x ∉ ys
∉∷₂ {A = A} = ¬∈→∉ {ℙA = Finset A} λ H∈ → ∉→¬∈ {ℙA = Finset A} auto (thereₛ H∈)

∉∪₁ :
  ⦃ _ : Discrete A ⦄
  {x : A}
  {xs ys : Finset A}
  (_ : x ∉ (xs <> ys))
  → ---------------------
  x ∉ xs
∉∪₁ {A = A} p = ¬∈→∉ {ℙA = Finset A} λ H∈ →
  ∉→¬∈ {ℙA = Finset A} p (unionl-∈ᶠˢ _ _ _ H∈)

∉∪₂ :
  ⦃ _ : Discrete A ⦄
  {x : A}
  (xs : Finset A)
  {ys : Finset A}
  (_ : x ∉ (xs <> ys))
  → ---------------------
  x ∉ ys
∉∪₂ {A = A} xs p = ¬∈→∉ {ℙA = Finset A} λ H∈ →
  ∉→¬∈ {ℙA = Finset A} p (unionr-∈ᶠˢ _ xs _ H∈)

∉∪ :
  ⦃ _ : Discrete A ⦄
  {x : A}
  {xs ys : Finset A}
  (_ : x ∉ xs)
  (_ : x ∉ ys)
  → ---------------------
  x ∉ (xs <> ys)
∉∪ {A = A} p q = ¬∈→∉ {ℙA = Finset A} λ H∈ →
  ∥-∥-rec
   (hlevel 1)
   (λ { (inl ∈xs) → ∉→¬∈ {ℙA = Finset A} p ∈xs
      ; (inr ∈ys) → ∉→¬∈ {ℙA = Finset A} q ∈ys
      })
   (∈ᶠˢ-union _ _ _ H∈)

∉-minus :
  ⦃ _ : Discrete A ⦄
  {xs : Finset A}
  {x y : A}
  (_ : y ∉ (xs -[ x ]))
  (_ : ¬ y ≡ x)
  → -----------------
  y ∉ xs
∉-minus {A = A} H∉ H≠ = ¬∈→∉ {ℙA = Finset A} λ H∈ →
  ∉→¬∈ {ℙA = Finset A} H∉ (filter-∈ᶠˢ _ H∈ H≠)

map-∉ :
  {ℓ : Level}
  {A B : Type ℓ}
  ⦃ _ : Discrete A ⦄
  ⦃ _ : Discrete B ⦄
  {f : A → B}
  {x : A}
  {xs : Finset A}
  ⦃ p : f x ∉ map f xs ⦄
  → --------------------
  x ∉ xs
map-∉ {A = A} {B = B} ⦃ p = p ⦄ =
  ¬∈→∉ {ℙA = Finset A} λ q → ∉→¬∈ {ℙA = Finset B} p (map-∈ᶠˢ _ _ q)

module FinsetSyntax where
  pattern Ø = []
  pattern [_] a = a ∷ []

  _∪_ : Finset A → Finset A → Finset A
  _∪_ = _<>_
