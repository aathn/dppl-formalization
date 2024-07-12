--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.Shift where

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.Freshness
open import Lib.LocalClosedness
open import Lib.Support
open import Lib.AbstractionConcretion
open import Lib.RenamingReindexingSwapping
open import Lib.Category

----------------------------------------------------------------------
-- Shift functor [Section 3.4]
----------------------------------------------------------------------
oc↑ : {X : Set}{{_ : oc X}} → oc X
lns↑ : {X : Set}{{_ : lns X}} → lns X

_~>_ {{oc↑}} i a x           = (i +1 ~> a)x -- Equation (56)
_<~_ {{oc↑}} i a x           = (i +1 <~ a)x -- Equation (56)
oc₁  {{oc↑}} i a b x         = oc₁ (i +1) a b x
oc₂  {{oc↑}} i j a x         = oc₂ (i +1) (j +1) a x
oc₃  {{oc↑}} i a x           = oc₃ (i +1) a x
oc₄  {{oc↑}} i a x           = oc₄ (i +1) a x
oc₅  {{oc↑}} i j a b x {{p}} =
  oc₅ (i +1) (j +1) a b x {{+1≠ {i} {j} p}}
oc₆  {{oc↑}} i j a b x       =
  oc₆ (i +1) (j +1) a b x {{it}}
oc₇  {{oc↑}} i j a b x {{p}} =
  oc₇ (i +1) (j +1) a b x {{+1≠ {i} {j} p}} {{it}}
oc₈  {{oc↑}} i j a b x       = oc₈ (i +1) (j +1) a b x
oc₉  {{oc↑}} i j a b x       = oc₉ (i +1) (j +1) a b x
ocSet {{lns↑}} = oc↑
asupp {{lns↑}} x with Иi и₁ и₂ ← asupp x = Иi и₁ и₂'
  where
  и₂' : (a : 𝔸){{_ : a ∉ и₁}} → (1 <~ a) x ≡ x
  и₂' a = #1 {j = 1} (и₂ a {{it}})
isupp {{lns↑}} x with (i , p) ← isupp x = (pred i , f)
  where
  f :
    (j : ℕ)
    {{_ : pred i ≤ j}}
    → ----------------------------
    ∑ a ∶ 𝔸 , (((j +1) ~> a)x ≡ x)
  f j {{q}} = p (j +1) {{≤trans (pred+1≤ i) (+1≤ q)}}

----------------------------------------------------------------------
-- Iterated shift [Equations (60)]
----------------------------------------------------------------------
oc⇑ : {n : ℕ}{X : Set}{{_ : oc X}} → oc X
oc⇑ {0}    {{p}} = p
oc⇑ {n +1} {{p}} = oc↑ {{oc⇑{n}{{p}}}}

lns⇑ : {n : ℕ}{X : Set}{{_ : lns X}} → lns X
lns⇑ {0}    {{p}} = p
lns⇑ {n +1} {{p}} = lns↑ {{lns⇑{n}{{p}}}}
