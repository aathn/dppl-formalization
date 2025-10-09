module Lib.Order.Bool where

open import Cat.Instances.Shape.Interval public using (Bool-poset)
open import Data.Bool.Base
open import Data.Bool.Order
open import Data.Dec.Base
open import Order.Diagram.Top
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Semilattice.Join
open import Order.Semilattice.Meet

Bool-has-top : Top Bool-poset
Bool-has-top .Top.top = true
Bool-has-top .Top.has-top true  = _
Bool-has-top .Top.has-top false = _

Bool-has-bot : Bottom Bool-poset
Bool-has-bot .Bottom.bot = false
Bool-has-bot .Bottom.has-bottom true  = _
Bool-has-bot .Bottom.has-bottom false = _

Bool-has-joins : ∀ a b → is-join Bool-poset a b (or a b)
Bool-has-joins a b .is-join.l≤join = or-≤l a b
Bool-has-joins a b .is-join.r≤join = or-≤r a b
Bool-has-joins a b .is-join.least c = or-univ c a b

Bool-has-meets : ∀ a b → is-meet Bool-poset a b (and a b)
Bool-has-meets a b .is-meet.meet≤l = and-≤l a b
Bool-has-meets a b .is-meet.meet≤r = and-≤r a b
Bool-has-meets a b .is-meet.greatest c = and-univ c a b

open is-meet-semilattice
open is-join-semilattice

Bool-is-meet-slat : is-meet-semilattice Bool-poset
Bool-is-meet-slat ._∩_ x y = and x y
Bool-is-meet-slat .∩-meets = Bool-has-meets
Bool-is-meet-slat .has-top = Bool-has-top

Bool-is-join-slat : is-join-semilattice Bool-poset
Bool-is-join-slat ._∪_ x y    = or x y
Bool-is-join-slat .∪-joins    = Bool-has-joins
Bool-is-join-slat .has-bottom = Bool-has-bot

instance
  DecOrd-Bool : ∀ {a b} → Dec (a ≤ b)
  DecOrd-Bool {false} {_}    = yes (lift _)
  DecOrd-Bool {true} {true}  = yes (lift _)
  DecOrd-Bool {true} {false} = no λ ()
