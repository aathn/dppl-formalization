open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br

import Lib.Cat.Bi.Adjoint as Adj

module Lib.Cat.Bi.Equivalence where

private variable
  o o' h h' ℓ ℓ' : Level
  B C : Prebicategory o h ℓ

module _ (C : Prebicategory o h ℓ) where
  open Prebicategory C
  private
    module C  = Br C
    module CH = C.Hom

  record is-equivalence {A B} (f : A ↦ B) : Type (h ⊔ ℓ) where
    open Adj C
    field
      inv : B ↦ A
      inv-adjoint : f ⊣ inv

    open _⊣_ inv-adjoint public

    field
      unit-iso   : CH.is-invertible η
      counit-iso : CH.is-invertible ε

  record Equivalence A B : Type (h ⊔ ℓ) where
    field
      to : A ↦ B
      to-equiv : is-equivalence to

open Pseudonatural

is-equivalenceᵖ : {F G : Lax-functor B C} → F =>ₚ G → Type _
is-equivalenceᵖ {C = C} α = ∀ X → is-equivalence C (α .σ X)

record Equivalenceᵖ
  {o h ℓ o' h' ℓ'} {B : Prebicategory o h ℓ} {C : Prebicategory o' h' ℓ'}
  (F : Lax-functor B C) (G : Lax-functor B C) : Type (o ⊔ h ⊔ ℓ ⊔ h' ⊔ ℓ')
  where
  field
    to : F =>ₚ G
    to-equiv : is-equivalenceᵖ to
