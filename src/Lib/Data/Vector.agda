module Lib.Data.Vector where

open import 1Lab.Prelude

open import Lib.Data.Fin

open import Data.Fin.Base
  using (Fin ; fzero ; fsuc ; fin-view ; zero ; suc ; split-+ ; fshift ; inject ; Fin-cases)
open import Data.Fin.Base public using (_[_≔_] ; delete)
open import Data.Fin.Properties
  using (insert-delete ; insert-lookup ; avoid-insert ; skip-avoid ; delete-insert)
open import Data.Nat.Properties using (+-≤l)
open import Data.Sum.Base using (inl ; inr ; ⊎-map)

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
foldr {n = zero} f z xs = z
foldr {n = suc n} f z xs = f (head xs) (foldr f z (tail xs))

_++_ : A ^ m → A ^ n → A ^ (m + n)
(xs ++ ys) i with split-+ i
... | inl j = xs j
... | inr k = ys k

split : ∀ m → A ^ (m + n) → A ^ m × A ^ n
split {n = n} m as = as ∘ inject (+-≤l _ _) , as ∘ fshift m

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

++-singleton : {x : A} {xs : A ^ m} → make x ++ xs ≡ x ∷ xs
++-singleton = funext $ Fin-cases refl λ _ → refl

++-split : ∀ m (x : A ^ (m + n)) → uncurry _++_ (split m x) ≡ x
++-split m x = ext go where
  go : ∀ i → uncurry _++_ (split m x) i ≡ x i
  go i with split-+ {m} i in Heq
  ... | inl j = ap x (split-+-inl Heq)
  ... | inr j = ap x (split-+-inr Heq)

split-++ : (xy : A ^ m × A ^ n) → split m (uncurry _++_ xy) ≡ xy
split-++ {m = m} {n} xy = ext Hx ,ₚ ext Hy where
  Hx : Extensional-Π .Pathᵉ (split m (uncurry _++_ xy) .fst) (xy .fst)
  Hx i rewrite Id≃path.from (split-+-inject {n = n} i) = refl
  Hy : Extensional-Π .Pathᵉ (split m (uncurry _++_ xy) .snd) (xy .snd)
  Hy i rewrite Id≃path.from (split-+-fshift m i) = refl

vec-prod-sum : (A ^ m × A ^ n) ≃ A ^ (m + n)
vec-prod-sum .fst         = uncurry _++_
vec-prod-sum {m = m} .snd = is-iso→is-equiv $ iso (split m) (++-split m) split-++

----------------------------------------------------------------------
-- Arrays
----------------------------------------------------------------------
record Array {l : Level}(A : Type l) : Type l where
  constructor mkArray
  field
    length : Nat
    index  : A ^ length

open Array public
