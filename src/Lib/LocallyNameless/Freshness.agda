--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.LocallyNameless.Freshness where

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets

----------------------------------------------------------------------
-- Freshness [Section 2.3]
----------------------------------------------------------------------
infix 4 _#_
_#_ : {X : Type}⦃ _ : oc X ⦄ → 𝔸 → X → Type
a # x = (0 <~ a)x ≡ x -- Equation (3)

module _ {X : Type}⦃ _ : oc X ⦄ where
  #1 : -- Equation (4)
    {i j : Nat}
    {a : 𝔸}
    {x : X}
    (p : (i <~ a)x ≡ x)
    → -----------------
    (j <~ a)x ≡ x
  #1 {i = i} {j} {a} {x} p =
    (j <~ a)x           ≡˘⟨ ap (j <~ a) p ⟩
    (j <~ a)((i <~ a)x) ≡⟨ oc₂ _ _ _ _ ⟩
    (i <~ a)x           ≡⟨ p ⟩
    x                   ∎

  #2 : -- Lemma 2.4
    {a : 𝔸}
    {x : X}
    {i : Nat}
    (p : a # x)
    → -----------
    (i <~ a)x ≡ x
  #2 = #1

  #3 : -- Lemma 2.4, cont.
    {a : 𝔸}
    {x : X}
    {i : Nat}
    (p : (i <~ a)x ≡ x)
    → -----------------
    a # x
  #3 = #1

  close-open-var : -- Corollary 2.5
    {a : 𝔸}
    {x : X}
    {i : Nat}
    (p : a # x)
    → ---------------------
    (i <~ a)((i ~> a)x) ≡ x
  close-open-var {a} {x} {i} p =
    (i <~ a)((i ~> a)x) ≡⟨ oc₃ _ _ _ ⟩
    (i <~ a)x           ≡⟨ #1 p ⟩
    x                   ∎
