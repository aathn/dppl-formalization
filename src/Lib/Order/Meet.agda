open import Order.Diagram.Meet
open import Order.Base

module Lib.Order.Meet where

module _ {o ℓ} {P : Poset o ℓ} where

  is-meet-sym : ∀ {a b c} → is-meet P a b c → is-meet P b a c
  is-meet-sym glb .is-meet.meet≤l = is-meet.meet≤r glb
  is-meet-sym glb .is-meet.meet≤r = is-meet.meet≤l glb
  is-meet-sym glb .is-meet.greatest lb' p q = is-meet.greatest glb lb' q p
