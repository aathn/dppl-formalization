open import 1Lab.Prelude

open import Data.Dec.Base

open import Order.Instances.Pointwise.Diagrams
open import Order.Instances.Pointwise
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Instances.Lower
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

instance
  H-Level-Reg≤ : ∀ {n a b} → H-Level (a ≤ b) (1 + n)
  H-Level-Reg≤ = prop-instance ≤-thin

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
Close-downward .hom f .pres-≤ H≤ p =
  case p of λ y H≤' Hy → inc (y , ≤-trans H≤ H≤' , Hy)
Close-downward .pres-≤ H⊆ x p =
  case p of λ y H≤ Hy → inc (y , H≤ , H⊆ y Hy)

A↓ P↓ C↓ PC↓ Ø↓ : Reg↓.Ob
A↓  = ↓ Reg-poset A
P↓  = ↓ Reg-poset P
C↓  = ↓ Reg-poset C
PC↓ = P↓ ∪ C↓
Ø↓  = bot
