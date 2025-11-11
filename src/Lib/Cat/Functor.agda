module Lib.Cat.Functor where

open import 1Lab.Reflection.Copattern
open import 1Lab.Reflection

open import Cat.Prelude

private variable
  o ℓ : Level
  C D : Precategory o ℓ
  f g : Functor C D

open Functor

nat-idr-op-to   : f => g F∘ op Id → f => g
nat-idr-op-from : f F∘ op Id => g → f => g

unquoteDef nat-idr-op-to nat-idr-op-from = do
  define-eta-expansion nat-idr-op-to
  define-eta-expansion nat-idr-op-from
