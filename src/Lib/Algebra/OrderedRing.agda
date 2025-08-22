module Lib.Algebra.OrderedRing where

open import 1Lab.Prelude hiding (_*_ ; _+_)
open import Algebra.Ring
open import Data.Sum.Base using (_⊎_ ; inl ; inr)
open import Order.Base
import Order.Reasoning as Or
import Algebra.Ring.Reasoning as Rr


record is-ordered-ring {o ℓ} (P : Poset o ℓ) (R : Ring-on ⌞ P ⌟) : Type (o ⊔ ℓ) where
  open Poset P public
  open Ring-on R

  field
    -- We adopt a weaker definition of total order than Order.Total,
    -- postulating not an ordering procedure but a "mere" ordering.
    -- This is because we want to represent real numbers, where
    -- comparison is undecidable.
    compare        : (a b : ⌞ P ⌟) → ∥ a ≤ b ⊎ b ≤ a ∥
    +-preserves-≤r : (a b c : ⌞ P ⌟) → a ≤ b → (a + c) ≤ (b + c)
    *-preserves-0≤ : (a b : ⌞ P ⌟) → 0r ≤ a → 0r ≤ b → 0r ≤ (a * b)

  ring : Σ (Set o) λ X → Ring-on ∣ X ∣
  ring = el ⌞ P ⌟ has-is-set , R

record Ordered-ring-on {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  field
    has-ring-on : Ring-on ⌞ P ⌟
    has-is-ordered-ring : is-ordered-ring P has-ring-on

  open Ring-on has-ring-on public
  open is-ordered-ring has-is-ordered-ring public


module Reasoning {o ℓ} {P : Poset o ℓ} (R : Ordered-ring-on P) where
  open Ordered-ring-on R
  module R = Rr ring

  open Or P hiding (_≤_)

  a≤0→0≤-a : ∀ a → a ≤ 0r → 0r ≤ (- a)
  a≤0→0≤-a a H≤ =
    0r         =˘⟨ +-invr ⟩
    a + (- a)  ≤⟨ +-preserves-≤r _ _ _ H≤ ⟩
    0r + (- a) =⟨ +-idl ⟩
    - a        ≤∎

  0≤a² : ∀ a → 0r ≤ a * a
  0≤a² a = case compare 0r a of λ where
    (inl H≤) → *-preserves-0≤ _ _ H≤ H≤
    (inr H≤) →
      0r            ≤⟨ *-preserves-0≤ _ _ (a≤0→0≤-a _ H≤) (a≤0→0≤-a _ H≤) ⟩
      (- a) * (- a) =⟨ R.*-negatel ∙ ap -_ R.*-negater ⟩
      - (- (a * a)) =⟨ inv-inv ⟩
      a * a         ≤∎

  0≤1 : 0r ≤ 1r
  0≤1 =
    0r      ≤⟨ 0≤a² 1r ⟩
    1r * 1r =⟨ *-idr ⟩
    1r      ≤∎
