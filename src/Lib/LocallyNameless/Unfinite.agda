--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.LocallyNameless.Unfinite where

open import Lib.Prelude

open import Data.Finset.Base

----------------------------------------------------------------------
-- The property of being an unfinite set
----------------------------------------------------------------------
record Unfinite {l : Level}(A : Type l) : Type l where
  field
    ⦃ deceq ⦄ : Discrete A
    new       : Finset A → A
    unfinite  : (xs : Finset A) → new xs ∉ xs

open Unfinite ⦃ ... ⦄ public

----------------------------------------------------------------------
-- ℕ is unfinite
----------------------------------------------------------------------
instance
  Unfinite-Nat : Unfinite Nat
  deceq    ⦃ Unfinite-Nat ⦄    = auto
  new      ⦃ Unfinite-Nat ⦄ xs = suc (maxfs xs)
  unfinite ⦃ Unfinite-Nat ⦄    = maxfs+1∉

----------------------------------------------------------------------
-- Unfinite disjoint union
----------------------------------------------------------------------
Unfinite-⊎ :
  {l : Level}
  {A B : Type l}
  ⦃ _ : Discrete A ⦄
  ⦃ _ : Unfinite B ⦄
  → ----------------
  Unfinite (A ⊎ B)
deceq    ⦃ Unfinite-⊎ ⦄    = auto
new      ⦃ Unfinite-⊎ ⦄ xs = inr (new (inr⁻¹ xs))
unfinite ⦃ Unfinite-⊎ ⦄ xs =
  ∉inr⁻¹→inr∉ xs (new (inr⁻¹ xs)) (unfinite (inr⁻¹ xs))

----------------------------------------------------------------------
-- Supported sets over a given unfinite set
----------------------------------------------------------------------
record Supp {V : Type} ⦃ _ : Unfinite V ⦄ (S : Type) : Type where
  field
    § : S → Finset V

open Supp ⦃ ... ⦄ public

{-# DISPLAY Supp.§ _ s = § s #-}

instance
  SuppV : {V : Type} ⦃ _ : Unfinite V ⦄ → Supp V
  § ⦃ SuppV ⦄ x = x ∷ []

  SuppFinsetV : {V : Type} ⦃ _ : Unfinite V ⦄ → Supp (Finset V)
  § ⦃ SuppFinsetV ⦄ xs = xs

  Supp× :
    {V : Type}
    ⦃ _ : Unfinite V ⦄
    {S S' : Type}
    ⦃ _ : Supp {V} S ⦄
    ⦃ _ : Supp {V} S' ⦄
    → ----------------
    Supp{V} (S × S')
  § ⦃ Supp× ⦄ (s , s') = § s <> § s'

fresh :
  {V : Type}
  ⦃ _ : Unfinite V ⦄
  {S : Type}
  ⦃ _ : Supp S ⦄
  (s : S)
  → ----------------
  Σ[ u ∈ V ] u ∉ § s
fresh s = (new (§ s) , unfinite (§ s))

----------------------------------------------------------------------
-- Atoms [Section 2.1]
----------------------------------------------------------------------
{- The original paper uses a presentation of atoms as nested finite
sets, but showing decidable equality for such a type is a bit fiddly
when working with actual sets in the cubical setting, so we simply use
natural numbers instead.
-}

opaque
  𝔸 : Type
  𝔸 = Nat

  instance
    Discrete-𝔸 : Discrete 𝔸
    Discrete-𝔸 = Discrete-Nat

  instance
    Unfinite-𝔸 : Unfinite 𝔸
    Unfinite-𝔸 = Unfinite-Nat

----------------------------------------------------------------------
-- Cofinite quantifer ("for all but finitely many...") [Definition 2.1]
----------------------------------------------------------------------
infix 2 Cof
record Cof
  {l : Level}
  (A : Type l)
  ⦃ _ : Discrete A ⦄
  (P : A → Type l)
  : ----------------
  Type l
  where
  constructor Иi
  field
    Иe₁ : Finset A
    Иe₂ : (x : A) → ⦃ x ∉ Иe₁ ⦄ → P x

open Cof public

syntax Cof A (λ x → P) = И[ x ∈ A ] P
