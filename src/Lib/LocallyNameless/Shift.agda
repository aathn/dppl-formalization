--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.LocallyNameless.Shift where

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets
open import Lib.LocallyNameless.Freshness
open import Lib.LocallyNameless.LocalClosedness
open import Lib.LocallyNameless.Support
open import Lib.LocallyNameless.AbstractionConcretion
open import Lib.LocallyNameless.RenamingReindexingSwapping
open import Lib.LocallyNameless.Category

open import Data.Nat.Base using (pred ; suc-inj)

open NatOrd

----------------------------------------------------------------------
-- Shift functor [Section 3.4]
----------------------------------------------------------------------
oc↑ : {X : Type}⦃ _ : oc X ⦄ → oc X
lns↑ : {X : Type}⦃ _ : lns X ⦄ → lns X

_~>_ ⦃ oc↑ ⦄ i a x           = (suc i ~> a)x -- Equation (56)
_<~_ ⦃ oc↑ ⦄ i a x           = (suc i <~ a)x -- Equation (56)
oc₁  ⦃ oc↑ ⦄ i a b x         = oc₁ (suc i) a b x
oc₂  ⦃ oc↑ ⦄ i j a x         = oc₂ (suc i) (suc j) a x
oc₃  ⦃ oc↑ ⦄ i a x           = oc₃ (suc i) a x
oc₄  ⦃ oc↑ ⦄ i a x           = oc₄ (suc i) a x
oc₅  ⦃ oc↑ ⦄ i j a b x =
  oc₅ (suc i) (suc j) a b x ⦃ inj≠ suc-inj auto ⦄
oc₆  ⦃ oc↑ ⦄ i j a b x       =
  oc₆ (suc i) (suc j) a b x
oc₇  ⦃ oc↑ ⦄ i j a b x =
  oc₇ (suc i) (suc j) a b x ⦃ inj≠ suc-inj auto ⦄
oc₈  ⦃ oc↑ ⦄ i j a b x       = oc₈ (suc i) (suc j) a b x
oc₉  ⦃ oc↑ ⦄ i j a b x       = oc₉ (suc i) (suc j) a b x
ocSet ⦃ lns↑ ⦄ = oc↑
asupp ⦃ lns↑ ⦄ x with Иi и₁ и₂ ← asupp x = Иi и₁ и₂'
  where
  и₂' : (a : 𝔸)⦃ _ : a ∉ и₁ ⦄ → (1 <~ a) x ≡ x
  и₂' a = #1 {j = 1} (и₂ a)
isupp ⦃ lns↑ ⦄ x with (i , p) ← isupp x = (pred i , f)
  where
  f :
    (j : Nat)
    ⦃ _ : pred i ≤ j ⦄
    → ----------------------------
    Σ[ a ∈ 𝔸 ] (suc j ~> a)x ≡ x
  f j = p (suc j) ⦃ ≤-trans i≤spi auto ⦄ where
    i≤spi : ∀ {i} → i ≤ suc (pred i)
    i≤spi {zero} = 0≤x
    i≤spi {suc i} = ≤-refl

----------------------------------------------------------------------
-- Iterated shift [Equations (60)]
----------------------------------------------------------------------
oc⇑ : {n : Nat}{X : Type}⦃ _ : oc X ⦄ → oc X
oc⇑ {0}    ⦃ p ⦄ = p
oc⇑ {suc n} ⦃ p ⦄ = oc↑ ⦃ oc⇑{n}⦃ p ⦄ ⦄

lns⇑ : {n : Nat}{X : Type}⦃ _ : lns X ⦄ → lns X
lns⇑ {0}    ⦃ p ⦄ = p
lns⇑ {suc n} ⦃ p ⦄ = lns↑ ⦃ lns⇑{n}⦃ p ⦄ ⦄
