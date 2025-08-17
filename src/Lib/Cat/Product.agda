module Lib.Cat.Product where

open import Cat.Prelude
open import Cat.Functor.Naturality
open import Cat.Instances.Product
import Cat.Reasoning as Cr

open _=>_
open make-natural-iso

private variable
  o h : Level
  B B' C C' D D' : Precategory o h

_nt,_
  : {F G : Functor B C} {H K : Functor B D}
  → F => G → H => K → Cat⟨ F , H ⟩ => Cat⟨ G , K ⟩
_nt,_ α β .η c = α .η c , β .η c
_nt,_ α β .is-natural _ _ f = Σ-pathp
  (α .is-natural _ _ f)
  (β .is-natural _ _ f)

F×-interchange
  : (F : Functor C D) (G : Functor C' D')
  → (H : Functor B C) (K : Functor B' C')
  → ((F F∘ H) F× (G F∘ K)) ≅ⁿ (F F× G) F∘ (H F× K)
F×-interchange {D = D} {D' = D'} F G H K = to-natural-iso ni where
  open Cr (D ×ᶜ D')
  ni : make-natural-iso _ _
  ni .eta _ = id
  ni .inv _ = id
  ni .eta∘inv _ = idl _
  ni .inv∘eta _ = idl _
  ni .natural _ _ f = id-comm
