module Lib.Cat.Sites where

open import Lib.Cat.Concrete

open import Cat.Prelude
open import Cat.Diagram.Limit.Cone
open import Cat.Diagram.Sieve
open import Cat.Finite
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Cat.Functor.Constant
open import Cat.Site.Base
import Cat.Reasoning as Reasoning

open _=>_

-- We define the notion of a (concrete) site morphism, the bicategory
-- of concrete sites, and show the existence of oplax colimits in this
-- bicategory.

-- First, we must define the notion of flatness which forms a
-- principal part of the definition.
--
-- golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html
-- https://ncatlab.org/nlab/show/flat+functor#SiteValuedFunctors


module _ {oc ℓc oe ℓe ℓcov}
  {C : Precategory oc ℓc}
  {E : Precategory oe ℓe}
  {J : Coverage E ℓcov}
  (F : Functor C E)
  where
  open Coverage J
  module F = Functor F
  module C = Precategory C
  module E = Precategory E

  cone-sieve
    : ∀ {oj} {ℓj} {I : Precategory oj ℓj} (D : Functor I C) {U : ⌞ E ⌟} (T : Const U => F F∘ D)
    → Sieve E U
  cone-sieve D T .arrows {V} h =
    elΩ $ Σ[ w ∈ C ] Σ[ S ∈ Const w => D ] Σ[ g ∈ Const V => F F∘ Const w ]
          T ∘nt constⁿ h ≡ (F ▸ S) ∘nt g
  cone-sieve D T .closed hh g = do
    w , S , g' , p ← hh
    inc (w , S , g' ∘nt constⁿ g , ext λ i → extendl (p ηₚ i))
    where open Reasoning E

  is-flat : ∀ {oj ℓj} → Type _
  is-flat {oj} {ℓj} =
    ∀ {I : Precategory oj ℓj} {I-fin : is-finite-precategory I} (D : Functor I C) {U : ⌞ E ⌟} (T : Const U => F F∘ D)
    → ∃[ S ∈ J ʻ U ] ⟦ S ⟧ ⊆ cone-sieve D T
