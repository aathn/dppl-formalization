module Lib.Data.Nat where

open import 1Lab.Prelude
open import Lib.Data.Vector

open import Data.Fin using (Fin ; fin-view ; zero ; suc)
open import Data.Nat.Properties using (+-commutative ; monus-swapr)

module NatOrd where
  open import Data.Nat.Base public
    using (_≤_ ; s≤s ; ≤-trans ; _<_ ; max)
  open import Data.Nat.Properties public
    using (max-≤l ; max-≤r ; max-univ)
  open import Data.Nat.Order public using (≤-refl)

  _≥_ = flip _≤_
  _>_ = flip _<_

open NatOrd

monus-preserves-≤ : ∀ x y z → x ≤ y → x - z ≤ y - z
monus-preserves-≤ x y zero H≤ = H≤
monus-preserves-≤ zero y (suc z) H≤ = 0≤x
monus-preserves-≤ (suc x) (suc y) (suc z) (s≤s H≤) = monus-preserves-≤ x y z H≤

monus-adj : ∀ x y z → x + y ≤ z → x ≤ z - y
monus-adj x y z H≤ =
  subst (λ x → x ≤ z - y) (sym $ monus-swapr _ y _ refl)
  (monus-preserves-≤ (x + y) z y H≤)

Max : {n : Nat} → Nat ^ n → Nat
Max = foldr max 0

≤-Max :
  {n : Nat}
  (f : Nat ^ n)
  (k : Fin n)
  → -------------
  f k ≤ Max f
≤-Max f k with fin-view k
... | zero  = max-≤l _ _
... | suc k = ≤-trans (≤-Max (tail f) k) (max-≤r _ _)
