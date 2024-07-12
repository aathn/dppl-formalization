--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.FunExt where

open import Lib.Prelude

----------------------------------------------------------------------
-- Postulated function extensionality
----------------------------------------------------------------------
postulate
  funext :
    {l m : Level}
    {A : Set l}
    {B : A → Set m}
    {f g : (x : A) → B x}
    (_ : ∀ x → f x ≡ g x)
    → -------------------
    f ≡ g
----------------------------------------------------------------------
--  Function extensionality with instance arguments
----------------------------------------------------------------------
instance-funext :
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  {f g : {{x : A}} → B x}
  (_ : ∀ x → f {{x}} ≡ g {{x}})
  → --------------------------------------
  (λ{{x}} → f {{x}}) ≡ (λ{{x}} → g {{x}})
instance-funext {A = A} {B} {f} {g} e =
  ap inst (funext {f = λ x → f{{x}}} {g = λ x → g{{x}}} e)
  where
  inst : ((x : A) → B x) → {{x : A}} → B x
  inst f {{x}} = f x
