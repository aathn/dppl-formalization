module Lib.Cat.Product where

open import Cat.Prelude
open import Cat.Instances.Product

open _=>_

private variable
  o₁ h₁ : Level
  B C D : Precategory o₁ h₁

_nt,_
  : {F G : Functor B C} {H K : Functor B D}
  → F => G → H => K → Cat⟨ F , H ⟩ => Cat⟨ G , K ⟩
_nt,_ α β .η c = α .η c , β .η c
_nt,_ α β .is-natural _ _ f = Σ-pathp
  (α .is-natural _ _ f)
  (β .is-natural _ _ f)
