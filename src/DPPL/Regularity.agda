module DPPL.Regularity where

open import Lib.Data.Dec hiding (_≠_)
open import Lib.Order.Bool
open import Lib.Order.Monotone
import Lib.Order.Wide as Wide

open import 1Lab.Prelude
open import Data.Bool.Base
open import Data.Bool.Order using (implies→≤)
open import Data.Dec.Base
open import Data.Fin.Finite
open import Order.Base
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Lattice
open import Order.Instances.Pointwise

data Reg : Type where
  A : Reg
  P : Reg
  C : Reg
  M : Reg

Reg≃Bool×Bool : Reg ≃ (Bool × Bool)
Reg≃Bool×Bool .fst A = true  , true
Reg≃Bool×Bool .fst P = true  , false
Reg≃Bool×Bool .fst C = false , true
Reg≃Bool×Bool .fst M = false , false
Reg≃Bool×Bool .snd = is-iso→is-equiv record
    { from = λ where
      (true  , true)  → A
      (true  , false) → P
      (false , true)  → C
      (false , false) → M
    ; rinv = λ where
      (true  , true)  → refl
      (true  , false) → refl
      (false , true)  → refl
      (false , false) → refl
    ; linv = λ where
      A → refl
      P → refl
      C → refl
      M → refl
    }

instance
  Listing-Reg : Listing Reg
  Listing-Reg = Equiv→listing (Equiv.inverse Reg≃Bool×Bool) auto

instance
  Discrete-Reg : Discrete Reg
  Discrete-Reg = Listing→Discrete auto

Reg-is-set : is-set Reg
Reg-is-set = Discrete→is-set Discrete-Reg

instance
  H-Level-Reg : ∀ {n} → H-Level Reg (2 + n)
  H-Level-Reg = basic-instance 2 Reg-is-set

instance
  Finite-Reg : Finite Reg
  Finite-Reg = inc auto

A≠M : A ≠ M
A≠M p = subst (λ {A → ⊤ ; _ → ⊥}) p tt

open Wide A M A≠M using (Wide ; DecOrd-Wide)

Reg-poset : Poset lzero lzero
Reg-poset = Wide

module Reg≤ = Poset Reg-poset

abstract
  Reg↓-poset : Poset lzero lzero
  Reg↓-poset = Poset[ Reg-poset ^opp , Bool-poset ]

  module Reg↓≤ = Poset Reg↓-poset

Reg↓ : Type
Reg↓ = Reg↓≤.Ob

abstract
  instance
    Discrete-Reg↓ : Discrete Reg↓
    Discrete-Reg↓ .decide x y with x .hom ≡? y .hom
    ... | yes x≡y = yes (ext (x≡y $ₚ_))
    ... | no  x≠y = no  (x≠y ∘ ap hom)

  Reg↓-meets : (a b : Reg↓) → Meet Reg↓-poset a b
  Reg↓-meets a b = Monotone-meets a b λ where
    x .Meet.glb      → and (a · x) (b · x)
    x .Meet.has-meet → Bool-has-meets _ _

  Reg↓-joins : (a b : Reg↓≤.Ob) → Join Reg↓-poset a b
  Reg↓-joins a b = Monotone-joins a b λ where
    x .Join.lub      → or (a · x) (b · x)
    x .Join.has-join → Bool-has-joins _ _

  Reg↓-lattice : is-lattice Reg↓-poset
  Reg↓-lattice = lat where
    open is-lattice
    lat : is-lattice Reg↓-poset
    lat ._∩_ a b = Meet.glb (Reg↓-meets a b)
    lat .∩-meets a b = Meet.has-meet (Reg↓-meets a b)
    lat ._∪_ a b = Join.lub (Reg↓-joins a b)
    lat .∪-joins a b = Join.has-join (Reg↓-joins a b)
    lat .has-top = Monotone-has-top Bool-has-top
    lat .has-bottom = Monotone-has-bot Bool-has-bot

  open is-lattice Reg↓-lattice

open Reg≤

abstract
  ↓ : Reg → Reg↓≤.Ob
  ↓ a .hom r = Dec→Bool (holds? (r ≤ a))
  ↓ a .pres-≤ y≤x = implies→≤ λ p →
    is-yes-so (true-is-yes (≤-trans y≤x (is-yes-true (so-is-yes p))))

  ↓-mono : Monotone Reg-poset Reg↓-poset
  ↓-mono .hom = ↓
  ↓-mono .pres-≤ x≤y a = implies→≤ λ p →
    is-yes-so (true-is-yes (≤-trans (is-yes-true (so-is-yes p)) x≤y))

  instance
    DecOrd-Reg↓ : ∀ {a} {b} → Dec (a Reg↓≤.≤ b)
    DecOrd-Reg↓ = Listing→Π-dec

  A↓-is-top : top ≡ ↓ A
  A↓-is-top = ext λ _ → refl

A↓ P↓ C↓ PC↓ M↓ Ø↓ : Reg↓
A↓  = ↓ A
P↓  = ↓ P
C↓  = ↓ C
PC↓ = P↓ ∪ C↓
M↓  = ↓ M
Ø↓  = bot

