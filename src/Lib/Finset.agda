module Lib.Finset where

open import 1Lab.Prelude
open import Data.Finset.Base

open import Order.Base using (Poset)
open import Order.Diagram.Join using (Join)
open import Order.Instances.Nat using (Nat-poset; Nat-joins; Nat-bottom)
open import Order.Semilattice.Join using (is-join-semilattice)
open import Data.Nat.Base using (max)
open import Data.Nat.Order using (¬sucx≤x)

private variable
  o ℓ : Level

module _ {P : Poset o ℓ} ⦃ joins : is-join-semilattice P ⦄ where
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
maxfs xs = fold xs

maxfs+1∉ : ∀ xs → suc (maxfs xs) ∉ xs
maxfs+1∉ xs H∈ = ¬sucx≤x _ (≤fold H∈)
