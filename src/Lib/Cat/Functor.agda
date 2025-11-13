module Lib.Cat.Functor where

open import 1Lab.Reflection.Copattern
open import 1Lab.Reflection

open import Cat.Prelude

private variable
  o ℓ : Level
  C D : Precategory o ℓ
  f g h : Functor C D

open Functor

nat-idr-op-to   : f => g F∘ op Id → f => g
nat-idr-op-from : f F∘ op Id => g → f => g
op-compose-from : Functor.op (f F∘ g) => h → Functor.op f F∘ Functor.op g => h

unquoteDef nat-idr-op-to nat-idr-op-from op-compose-from = do
  define-eta-expansion nat-idr-op-to
  define-eta-expansion nat-idr-op-from
  define-eta-expansion op-compose-from
