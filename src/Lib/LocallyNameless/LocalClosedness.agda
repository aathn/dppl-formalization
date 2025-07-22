--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.LocallyNameless.LocalClosedness where

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets

open NatOrd

----------------------------------------------------------------------
-- Local closedness [Section 2.4]
----------------------------------------------------------------------
infix 4 _≻_
_≻_ : {X : Type}⦃ _ : oc X ⦄ → Nat → X → Type
i ≻ x = (j : Nat)⦃ _ : j ≥ i ⦄ → Σ[ a ∈ 𝔸 ] (j ~> a)x ≡ x -- Equation (5)

module _ {X : Type}⦃ _ : oc X ⦄ where
  ≻1 : -- Lemma 2.6
    {i j : Nat}
    {x : X}
    (p : j ≥ i)
    (q : i ≻ x)
    → ---------
    j ≻ x
  ≻1 p q k = q k ⦃ ≤-trans p auto ⦄

  ≻2 : -- Equation (6)
    {i : Nat}
    {a b : 𝔸}
    {x : X}
    (p : (i ~> a)x ≡ x)
    → -----------------
    (i ~> b)x ≡ x
  ≻2 {i} {a} {b}{x} p =
      (i ~> b)x           ≡˘⟨ ap (i ~> b) p ⟩
      (i ~> b)((i ~> a)x) ≡⟨ oc₁ _ _ _ _ ⟩
      (i ~> a)x           ≡⟨ p ⟩
      x                   ∎

  ≻3 : -- Lemma 2.7
    {i j : Nat}
    {a : 𝔸}
    {x : X}
    (p : i ≻ x)
    (q : j ≥ i)
    → -----------
    (j ~> a)x ≡ x
  ≻3 p q = ≻2 (snd (p _ ⦃ q ⦄))

  open-close-var : -- Corollary 2.8
    {a : 𝔸}
    {x : X}
    {i : Nat}
    (p : i ≻ x)
    → ---------------------
    (i ~> a)((i <~ a)x) ≡ x
  open-close-var {a} {x} {i} p =
      (i ~> a)((i <~ a)x) ≡⟨ oc₄ _ _ _ ⟩
      (i ~> a)x           ≡⟨ ≻3 p ≤-refl ⟩
      x                   ∎
