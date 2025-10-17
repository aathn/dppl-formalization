module Lib.Data.Vector where

open import 1Lab.Prelude

open import Data.Fin.Base using (Fin ; fzero ; fsuc ; fin-view ; zero ; suc ; split-+)
open import Data.Sum.Base using (inl ; inr)

open import Data.Fin.Base public using (_[_≔_] ; delete)
open import Data.Fin.Properties using (insert-delete ; insert-lookup)

Vector : {l : Level} → Type l → Nat → Type l
Vector A n = Fin n → A

_^_ = Vector

private variable
  l l' : Level
  A : Type l
  B : Type l'
  n m : Nat

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
foldr {n = zero} f z xs = z
foldr {n = suc n} f z xs = f (head xs) (foldr f z (tail xs))

_++_ : A ^ n → A ^ m → A ^ (n + m)
(xs ++ ys) i with split-+ i
... | inl j = xs j
... | inr k = ys k

updateAt : A ^ n → Fin n → A → A ^ n
updateAt {n = suc n} xs i x = delete xs i [ i ≔ x ]

updateAt-id-local
  : ∀ {n} {ℓ} {A : Type ℓ}
  → (ρ : A ^ n)
  → (i : Fin n) (a : A)
  → ρ i ≡ a
  → ∀ j → updateAt ρ i a j ≡ ρ j
updateAt-id-local {suc n} = insert-delete

updateAt-updates
  : ∀ {n} {ℓ} {A : Type ℓ}
  → (ρ : A ^ n)
  → (i : Fin n) (a : A)
  → updateAt ρ i a i ≡ a
updateAt-updates {suc n} ρ i a = insert-lookup _ i a

----------------------------------------------------------------------
-- Arrays
----------------------------------------------------------------------
record Array {l : Level}(A : Type l) : Type l where
  constructor mkArray
  field
    length : Nat
    index  : A ^ length

open Array public
