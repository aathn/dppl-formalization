module DPPL.Denotations.Test where

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Product.Finite
open import Cat.Diagram.Product.Indexed
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Instances.Sheaf.Limits.Finite
open import Cat.Site.Base

open import Data.Fin.Base

module Bug {C : Precategory lzero lzero} (J : Coverage C lzero) (⋆ : ⌞ C ⌟) where

  module C = Precategory C
  open Cartesian-category (Sh[]-cartesian J)

  module ip {n} (F : Fin n → Ob) =
    Indexed-product (Cartesian→standard-finite-products terminal products F)


-- (Conc-よ₀ ℛ-conc ⋆ ⊗₀ 𝔇-ip.ΠF (make {n = n} top))
  bug : (n : Nat) → Type
  bug n =
    Hom
      (top ⊗₀ ((よ₀ C ⋆ , {!!}) ⊗₀ ip.ΠF (λ (_ : Fin n) → top)) ⊗₀ top)
      top
  
  -- record MyRecord : Type where
  --   field
  --     my-field : (n : Nat) → bug n
