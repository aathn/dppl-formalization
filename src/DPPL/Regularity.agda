module DPPL.Regularity where

open import 1Lab.Prelude hiding (_==_)
open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Id.Base
open import Order.Base
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Lattice
open import Order.Instances.Lower
import Lib.Order.Wide as Wide

data Reg : Type where
  A : Reg
  P : Reg
  C : Reg
  M : Reg

_==_ : Reg → Reg → Bool
A == A = true
P == P = true
C == C = true
M == M = true
_ == _ = false

from-prim-eq : ∀ {x y} → So (x == y) → x ≡ᵢ y
from-prim-eq {A} {A} p = reflᵢ
from-prim-eq {P} {P} p = reflᵢ
from-prim-eq {C} {C} p = reflᵢ
from-prim-eq {M} {M} p = reflᵢ

to-prim-eq : ∀ {x y} → x ≡ᵢ y → So (x == y)
to-prim-eq {A} {A} p = oh
to-prim-eq {P} {P} p = oh
to-prim-eq {C} {C} p = oh
to-prim-eq {M} {M} p = oh

instance
  Discrete-Reg : Discrete Reg
  Discrete-Reg = Discreteᵢ→discrete go where
    go : ∀ x y → Dec (x ≡ᵢ y)
    go x y with oh? (x == y)
    ... | yes p = yes (from-prim-eq p)
    ... | no ¬p = no  (¬p ∘ to-prim-eq)

opaque
  Reg-is-set : is-set Reg
  Reg-is-set = Discrete→is-set Discrete-Reg

instance
  H-Level-Reg : ∀ {n} → H-Level Reg (2 + n)
  H-Level-Reg = basic-instance 2 Reg-is-set

A≠M : A ≠ M
A≠M p = subst (λ {A → ⊤ ; _ → ⊥}) p tt

Reg-poset : Poset lzero lzero
Reg-poset = Wide.Wide A M A≠M

module Reg≤ = Poset Reg-poset

Reg↓ : Type
Reg↓ = Lower-set Reg-poset

Reg↓-poset : Poset lzero lzero
Reg↓-poset = Lower-sets Reg-poset

module Reg↓≤ = Poset Reg↓-poset

Reg↓-lattice : is-lattice Reg↓-poset
Reg↓-lattice = lat where
  open is-lattice
  lat : is-lattice Reg↓-poset
  lat ._∩_ a b     = Meet.glb (Lower-sets-meets Reg-poset a b)
  lat .∩-meets a b = Meet.has-meet (Lower-sets-meets Reg-poset a b)
  lat ._∪_ a b     = Join.lub (Lower-sets-joins Reg-poset a b)
  lat .∪-joins a b = Join.has-join (Lower-sets-joins Reg-poset a b)
  lat .has-top     = Lower-sets-top Reg-poset
  lat .has-bottom  = Lower-sets-bottom Reg-poset

open is-lattice Reg↓-lattice

R↓ : Reg → Reg↓
R↓ = ↓ Reg-poset

R≤↓ : ∀ {a b} → a Reg≤.≤ b → R↓ a Reg↓≤.≤ R↓ b
R≤↓ = よₚ Reg-poset .pres-≤

A↓ P↓ C↓ PC↓ M↓ Ø↓ : Reg↓
A↓  = R↓ A
P↓  = R↓ P
C↓  = R↓ C
PC↓ = P↓ ∪ C↓
M↓  = R↓ M
Ø↓  = bot

A↓-is-top : top ≡ A↓
A↓-is-top = ext λ _ → Ω-ua (λ _ → inc Wide.x≤⊤) (λ _ → tt)
