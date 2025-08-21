module Lib.Cat.Product where

open import Cat.Prelude
open import Cat.Functor.Naturality
open import Cat.Functor.Naturality.Reflection
open import Cat.Instances.Product
import Cat.Reasoning as Cr

open _=>_
open Functor

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
  : {F : Functor C D} {G : Functor C' D'}
  → {H : Functor B C} {K : Functor B' C'}
  → ((F F∘ H) F× (G F∘ K)) ≅ⁿ (F F× G) F∘ (H F× K)
F×-interchange = trivial-isoⁿ!

×ᶜ-op : Functor (C ^op ×ᶜ D ^op) ((C ×ᶜ D) ^op)
×ᶜ-op .F₀ x = x
×ᶜ-op .F₁ f = f
×ᶜ-op .F-id = refl
×ᶜ-op .F-∘ _ _ = refl
