open import 1Lab.Prelude

open import Data.Fin.Properties
open import Data.Fin.Base
open import Data.Sum.Base

open import Lib.Data.Fin

module Lib.Data.Vector where

open Data.Fin.Base public using (_[_≔_] ; delete)

Vector : {l : Level} → Type l → Nat → Type l
Vector A n = Fin n → A

infixl 30 _^_
_^_ = Vector

private variable
  l l' : Level
  A : Type l
  B : Type l'
  m n : Nat

module VectorSyntax where

  [] : A ^ zero
  [] i with () ← fin-view i

  _∷_ : A → A ^ n → A ^ suc n
  (x ∷ xs) i with fin-view i
  ... | zero = x
  ... | suc j = xs j

open VectorSyntax

head : A ^ suc n → A
head = _$ fzero

tail : A ^ suc n → A ^ n
tail = _∘ fsuc

π[_] : Fin n → A ^ n → A
π[ i ] = _$ i

make : A → A ^ n
make x _ = x

instance
  Map-Vector : Map (eff (_^ n))
  Map-Vector = record { map = λ f xs → f ∘ xs }

foldr : (A → B → B) → B → A ^ n → B
foldr {n = zero}  f z xs = z
foldr {n = suc n} f z xs = f (head xs) (foldr f z (tail xs))

vec-sum-prod : ∀ m → A ^ (m + n) ≃ (A ^ m × A ^ n)
vec-sum-prod {n = n} m = →-ap (Fin-+-≃ m) id≃ ∙e ⊎-universal

split : A ^ (m + n) → A ^ m × A ^ n
split {m = m} = Equiv.to (vec-sum-prod m)

_++_ : A ^ m → A ^ n → A ^ (m + n)
_++_ {m = m} = curry (Equiv.from (vec-sum-prod m))

updateAt : A ^ n → Fin n → A → A ^ n
updateAt {n = suc n} xs i x = delete xs i [ i ≔ x ]

updateAt-id-local
  : (ρ : A ^ n)
  → (i : Fin n) (a : A)
  → ρ i ≡ a
  → ∀ j → updateAt ρ i a j ≡ ρ j
updateAt-id-local {n = suc n} = insert-delete

updateAt-updates
  : (ρ : A ^ n)
  → (i : Fin n) (a : A)
  → updateAt ρ i a i ≡ a
updateAt-updates {n = suc n} ρ i a = insert-lookup _ i a

updateAt-minimal
  : (ρ : Fin n → A)
  → (i : Fin n) (a : A)
  → (j : Fin n)
  → (i≠j : i ≠ j)
  → updateAt ρ i a j ≡ ρ j
updateAt-minimal {n = suc n} ρ i a j i≠j =
  avoid-insert _ i a j i≠j ∙ ap ρ (skip-avoid i j)

updateAt-updateAt
  : (ρ : A ^ n)
  → (i : Fin n) (a b : A)
  → (j : Fin n)
  → updateAt (updateAt ρ i b) i a j ≡ updateAt ρ i a j
updateAt-updateAt {n = suc n} ρ i a b j =
  ap (λ xs → (xs [ i ≔ a ]) j) (funext $ delete-insert _ i b)

∷-head-tail : (x : A ^ suc m) → head x ∷ tail x ≡ x
∷-head-tail {m = m} x = ext go where
  go : ∀ i → (head x ∷ tail x) i ≡ x i
  go i with fin-view i
  ... | zero  = refl
  ... | suc _ = refl

++-tail : (xs : A ^ suc m) (ys : A ^ n) → tail (xs ++ ys) ≡ tail xs ++ ys
++-tail {m = m} xs ys = ext go where
  eqₗ : {i : Fin (m + n)} {j : Fin m} → split-+ i ≡ᵢ inl j → split-+ (fsuc i) ≡ᵢ inl (fsuc j)
  eqₗ = apᵢ (⊎-map fsuc id)

  eqᵣ : {i : Fin (m + n)} {j : Fin n} → split-+ i ≡ᵢ inr j → split-+ (fsuc i) ≡ᵢ inr j
  eqᵣ = apᵢ (⊎-map fsuc id)

  go : ∀ i → (tail (xs ++ ys)) i ≡ (tail xs ++ ys) i
  go i with split-+ {m} i in Heq
  ... | inl _ rewrite eqₗ Heq = refl
  ... | inr _ rewrite eqᵣ Heq = refl

++-map : (xs : A ^ m) (ys : A ^ n) (f : A → B) → f ∘ (xs ++ ys) ≡ f ∘ xs ++ f ∘ ys
++-map {m = m} xs ys f = ext go where
  go : ∀ i → (f ∘ (xs ++ ys)) i ≡ (f ∘ xs ++ f ∘ ys) i
  go i with split-+ {m} i
  ... | inl _ = refl
  ... | inr _ = refl

++-singleton : {x : A} {xs : A ^ m} → make x ++ xs ≡ x ∷ xs
++-singleton = funext $ Fin-cases refl λ _ → refl

----------------------------------------------------------------------
-- Arrays
----------------------------------------------------------------------
record Array {ℓ} (A : Type ℓ) : Type ℓ where
  constructor mkArray
  field
    length : Nat
    index  : A ^ length

open Array public
