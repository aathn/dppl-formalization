open import 1Lab.Prelude

open import Data.Dec.Base

open import Lib.Homotopy.Join
open import Lib.Order.Meet

open import Order.Instances.Pointwise.Diagrams
open import Order.Instances.Pointwise
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Instances.Lower renaming (↓ to ↓ˡ)
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Lattice
open import Order.Base

import Lib.Order.Wide as Wide

module DPPL.Regularity where

data Reg : Type where
  A : Reg
  P : Reg
  C : Reg

private
  is-A is-P is-C : Reg → Type
  is-A A = ⊤
  is-A _ = ⊥
  is-P P = ⊤
  is-P _ = ⊥
  is-C C = ⊤
  is-C _ = ⊥

instance
  Discrete-Reg : Discrete Reg
  Discrete-Reg .decide = go where
    go : _
    go A A = yes refl
    go P P = yes refl
    go C C = yes refl
    go A P = no λ p → subst is-A p tt
    go A C = no λ p → subst is-A p tt
    go P A = no λ p → subst is-P p tt
    go P C = no λ p → subst is-P p tt
    go C A = no λ p → subst is-C p tt
    go C P = no λ p → subst is-C p tt

abstract
  Reg-is-set : is-set Reg
  Reg-is-set = Discrete→is-set Discrete-Reg

instance
  H-Level-Reg : ∀ {n} → H-Level Reg (2 + n)
  H-Level-Reg = basic-instance 2 Reg-is-set

Reg-poset : Poset lzero lzero
Reg-poset = Wide.Wide A

module Reg≤ = Poset Reg-poset

open Reg≤

Reg↓-poset : Poset lzero lzero
Reg↓-poset = Lower-sets Reg-poset

module Reg↓ = Poset Reg↓-poset

Reg↓ : Type
Reg↓ = ⌞ Reg↓-poset ⌟

Reg⊆-poset : Poset lzero lzero
Reg⊆-poset = Subsets Reg

module Reg⊆ = Poset Reg⊆-poset

Reg⊆ : Type
Reg⊆ = ⌞ Reg⊆-poset ⌟

Reg↓-lat : is-lattice Reg↓-poset
Reg↓-lat .is-lattice._∩_ a b     = Meet.glb (Lower-sets-meets Reg-poset a b)
Reg↓-lat .is-lattice.∩-meets a b = Meet.has-meet (Lower-sets-meets Reg-poset a b)
Reg↓-lat .is-lattice._∪_ a b     = Join.lub (Lower-sets-joins Reg-poset a b)
Reg↓-lat .is-lattice.∪-joins a b = Join.has-join (Lower-sets-joins Reg-poset a b)
Reg↓-lat .is-lattice.has-top     = Lower-sets-top Reg-poset
Reg↓-lat .is-lattice.has-bottom  = Lower-sets-bottom Reg-poset

module Reg↓-lat = is-lattice Reg↓-lat

Reg⊆-lat : is-lattice Reg⊆-poset
Reg⊆-lat = record
  { is-meet-semilattice Subsets-is-meet-slat
  ; is-join-semilattice Subsets-is-join-slat
  }

module Reg⊆-lat = is-lattice Reg⊆-lat

open Reg↓-lat

Forget-closure : Monotone Reg↓-poset Reg⊆-poset
Forget-closure .hom f     = f .hom
Forget-closure .pres-≤ Hf = Hf

Close-downward : Monotone Reg⊆-poset Reg↓-poset
Close-downward .hom f .hom x       = elΩ (Σ[ y ∈ Reg ] x ≤ y × ∣ f y ∣)
Close-downward .hom f .pres-≤ H≤ p = do
  (y , H≤' , Hy) ← p
  inc (y , ≤-trans H≤ H≤' , Hy)
Close-downward .pres-≤ H⊆ x p = do
  (y , H≤ , Hy) ← p
  inc (y , H≤ , H⊆ y Hy)

↓ : Reg → Reg↓
↓ = ↓ˡ Reg-poset

A↓ P↓ C↓ PC↓ Ø↓ : Reg↓.Ob
A↓  = ↓ A
P↓  = ↓ P
C↓  = ↓ C
PC↓ = P↓ ∪ C↓
Ø↓  = bot

_~ʳ_ : Reg⊆ → Reg⊆ → Type
X ~ʳ Y =
  (x : ∫ₚ X) (y : ∫ₚ Y) → x .fst ≤ y .fst →
  ∃[ z ∈ ∫ₚ (X Reg⊆-lat.∩ Y) ] x .fst ≤ z .fst × z .fst ≤ y .fst

is-meet-closed : Reg⊆ → Type
is-meet-closed X = (x x' : ∫ₚ X) →
    (∀ z → z ≤ x .fst → ¬ z ≤ x' .fst)
  ∗ (Σ[ m ∈ Meet Reg-poset (x .fst) (x' .fst) ] Meet.glb m ∈ X)

P-C-incomp : ∀ z → z ≤ P → ¬ z ≤ C
P-C-incomp z Hz Hz' = case Hz of λ where
  (inl p) → case Hz' of λ where
    (inl q) → subst is-C (sym q ∙ p) tt
    (inr q) → subst is-C q tt
  (inr p) → subst is-P p tt

Reg⊆-is-meet-closed : ∀ X → is-meet-closed X
Reg⊆-is-meet-closed X (x , Hx) (A , _) =
  inr (record { glb = x ; has-meet = le→is-meet (inr refl) } , Hx)
Reg⊆-is-meet-closed X (A , _) (x' , Hx') =
  inr (record { glb = x' ; has-meet = is-meet-sym (le→is-meet (inr refl)) } , Hx')
Reg⊆-is-meet-closed X (P , Hx) (P , _) =
  inr (record { glb = P ; has-meet = le→is-meet (inl refl) } , Hx)
Reg⊆-is-meet-closed X (C , Hx) (C , _) =
  inr (record { glb = C ; has-meet = le→is-meet (inl refl) } , Hx)
Reg⊆-is-meet-closed X (P , _) (C , _) = inl P-C-incomp
Reg⊆-is-meet-closed X (C , _) (P , _) = inl (flip ∘ P-C-incomp)
