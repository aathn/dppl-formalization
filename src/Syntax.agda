open import Lib.BindingSignature

module Syntax where

data Coeffect : Set where
  A : Coeffect
  B : Coeffect
  C : Coeffect

data Effect : Set where
  det : Effect
  rnd : Effect

-- data Ty : Set where
--   treal : 
