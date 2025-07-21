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

open import Lib.Finset

open import 1Lab.Prelude
open import Data.Finset.Base

open import Data.Dec.Base using (yes ; no ; Discrete ; Dec)
open import Data.Finset.Properties using (finset-ext)
open import Data.Nat.Base using (Nat)
open import Data.Sum.Base using (_⊎_; inr; inl)
open import Data.Sum.Properties using (Discrete-⊎)

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
{- We could just take atoms to be given by natural numbers, but it
seems more elegant to use what is effectively a W-type that emphasises
one of the key properties of atoms (apart from having decidable
equality), namely that they are "unfinite" in the sense that for every
finite set of atoms there is an atom not in that set. -}

data 𝔸 : Type where
  new𝔸 : Finset 𝔸 → 𝔸

new𝔸-inj : {xs ys : Finset 𝔸} → new𝔸 xs ≡ new𝔸 ys → xs ≡ ys
new𝔸-inj path = ap (λ {(new𝔸 xs) → xs}) path

open Discrete

-- Equality of atoms is decidable
private
  Dec-𝔸 : (x y : 𝔸) → Dec (x ≡ y)
  Dec-𝔸s : (xs ys : Finset 𝔸) → Dec (xs ≡ ys)
  
  Dec-𝔸 (new𝔸 xs) (new𝔸 ys) with Dec-𝔸s xs ys
  ... | no  H≢ = no (H≢ ∘ new𝔸-inj)
  ... | yes H≡ = yes (ap new𝔸 H≡)
  
  Dec-𝔸s [] [] = yes refl
  Dec-𝔸s [] (_ ∷ _) = no (∷≠[] ∘ sym)
  Dec-𝔸s (x ∷ xs) [] = no ∷≠[]
  Dec-𝔸s (x ∷ xs) (y ∷ ys)
    with Dec-𝔸 x y | Dec-𝔸s xs ys
  ... | yes p | yes q = yes (ap₂ _∷_ p q)
  ... | yes p | no ¬q = {!!}
  ... | no ¬p | yes q = {!!}
  ... | no ¬p | no ¬q = {!!}
  Dec-𝔸s [] (∷-dup x ys i) = {!!}
  Dec-𝔸s [] (∷-swap x y ys i) = {!!}
  Dec-𝔸s [] (squash ys ys₁ x y i i₁) = {!!}
  Dec-𝔸s (x ∷ xs) (∷-dup x₁ ys i) = {!!}
  Dec-𝔸s (x ∷ xs) (∷-swap x₁ y ys i) = {!!}
  Dec-𝔸s (x ∷ xs) (squash ys ys₁ x₁ y i i₁) = {!!}
  Dec-𝔸s (∷-dup x xs i) ys = {!!}
  Dec-𝔸s (∷-swap x y xs i) ys = {!!}
  Dec-𝔸s (squash xs xs₁ x y i i₁) ys = {!!}
-- deceq𝔸s Ø Ø = equ
-- deceq𝔸s [ x ] [ y ] with deceq𝔸 x y
-- ... | neq f = neq λ{refl → f refl}
-- ... | equ   = equ
-- deceq𝔸s (xs ∪ _ )  (ys ∪ _  ) with deceq𝔸s xs ys
-- deceq𝔸s (_  ∪ _ )  (_  ∪ _  ) | neq f = neq λ{ refl → f refl}
-- deceq𝔸s (_  ∪ xs') (_  ∪ ys') | equ with deceq𝔸s xs' ys'
-- deceq𝔸s (_  ∪ _ )  (_  ∪ _  ) | equ | neq g = neq λ p → g (∪inj₂ p)
-- deceq𝔸s (_  ∪ _ )  (_  ∪ _  ) | equ | equ = equ
-- deceq𝔸s Ø [ _ ] = neq λ()
-- deceq𝔸s Ø (_ ∪ _) = neq λ()
-- deceq𝔸s [ _ ] Ø = neq λ()
-- deceq𝔸s [ _ ] (_ ∪ _) = neq λ()
-- deceq𝔸s (_ ∪ _) Ø = neq λ()
-- deceq𝔸s (_ ∪ _) [ _ ] = neq λ()

-- import Relation.Binary.PropositionalEquality.Properties as ≡

-- instance
--   hasDecEq𝔸 : hasDecEq 𝔸
--   isEquivalence {{hasDecEq𝔸}} = ≡.isEquivalence
--   _≐_ {{hasDecEq𝔸}} = deceq𝔸
--   hasDecEqFset𝔸 : hasDecEq (Fset 𝔸)
--   isEquivalence {{hasDecEqFset𝔸}} = ≡.isEquivalence
--   _≐_ {{hasDecEqFset𝔸}} = deceq𝔸s

-- ----------------------------------------------------------------------
-- -- The "unfinite" property of atoms [Equation (1)]
-- ----------------------------------------------------------------------

-- -- A well-founded relation between atoms
-- data _≺_ : (a y : 𝔸) → Set where
--   ≺new𝔸 :
--     {a : 𝔸}
--     {as : Fset 𝔸}
--     (_ : a ∈ as)
--     → ------------
--     a ≺ new𝔸 as

-- ≺iswf : wf.iswf _≺_
-- ≺iswf (new𝔸 as) = wf.acc λ{(≺new𝔸 p) → α _ p}
--   where
--   α : ∀ a {as} → a ∈ as → wf.Acc _≺_ a
--   α a ∈[]     = ≺iswf a
--   α a (∈∪₁ p) = α a p
--   α a (∈∪₂ p) = α a p

-- instance
--   Unfinite𝔸 : Unfinite 𝔸
--   deceq    {{Unfinite𝔸}}    = hasDecEq𝔸
--   new      {{Unfinite𝔸}}    = new𝔸
--   unfinite {{Unfinite𝔸}} as =
--     ¬∈→∉ λ p → wf.irrefl _≺_ ≺iswf (new𝔸 as) (≺new𝔸 p)

-- ----------------------------------------------------------------------
-- -- Cofinite quantifer ("for all but finitely many...") [Definition 2.1]
-- ----------------------------------------------------------------------
-- infix 2 Cof
-- record Cof
--   {l : Level}
--   (A : Set l)
--   {{α : hasDecEq A}}
--   (P : A → Set l)
--   : ----------------
--   Set l
--   where
--   constructor Иi
--   field
--     Иe₁ : Fset A
--     Иe₂ : (x : A){{_ : x ∉ Иe₁}} → P x

-- open Cof public

-- syntax Cof A (λ x → P) = И x ∶ A , P
