open import Lib.Algebra.Reals
import DPPL.Denotations.Site as Site

module DPPL.Denotations.Test (R : Reals₀) (Ax : Site.SiteAssumptions R) where

open import Lib.Cat.Concrete

open import Cat.Prelude
open import Cat.Cartesian

open Site.Site R Ax

open Cartesian-category (ConcPSh-cartesian ℛ-conc)

bug : Type
bug =
  Hom
    (top ⊗₀ (Conc-よ₀ ℛ-conc ⋆ ⊗₀ Conc-よ₀ ℛ-conc ⋆) ⊗₀ top)
    top

record MyRecord : Type where
  no-eta-equality
  field
    -- The record field below triggers makes type checking eat 16GB
    my-field : bug

-- The postulate below is fine
-- postulate
--   foo : bug
