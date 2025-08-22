module DPPL.Regularity where

open import 1Lab.Prelude hiding (_==_)
open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Id.Base
open import Order.Base
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

Reg↓ : Poset lzero lzero
Reg↓ = Lower-sets Reg-poset
