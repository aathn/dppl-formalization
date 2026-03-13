module Lib.Cat.Product where

open import Lib.Data.Vector

open import Cat.Prelude
open import Cat.Cartesian
open import Cat.Diagram.Product.Finite
open import Cat.Diagram.Product.Indexed
open import Cat.Functor.Base
open import Cat.Functor.Naturality
open import Cat.Functor.Naturality.Reflection
open import Cat.Instances.Product
open import Cat.Monoidal.Base
open import Cat.Monoidal.Instances.Cartesian
open import Data.Fin.Base
import Cat.Reasoning as Cr
import Cat.Functor.Bifunctor as Bifunctor

open Cr._≅_
open Cr.Inverses
open _=>_
open Functor

private variable
  o h : Level
  B B' C C' D D' : Precategory o h

_,Iso_
  : {A A' : ⌞ C ⌟} {B B' : ⌞ D ⌟} → Cr._≅_ C A A' → Cr._≅_ D B B'
  → Cr._≅_ (C ×ᶜ D) (A , B) (A' , B')
(iA ,Iso iB) .to       = iA .to , iB .to
(iA ,Iso iB) .from     = iA .from , iB .from
(iA ,Iso iB) .inverses = λ where
  .invl → iA .invl ,ₚ iB .invl
  .invr → iA .invr ,ₚ iB .invr

_nt,_
  : {F G : Functor B C} {H K : Functor B D}
  → F => G → H => K → Cat⟨ F , H ⟩ => Cat⟨ G , K ⟩
_nt,_ α β .η c              = α .η c , β .η c
_nt,_ α β .is-natural _ _ f = α .is-natural _ _ f ,ₚ β .is-natural _ _ f

×ᶜ-op : Functor (C ^op ×ᶜ D ^op) ((C ×ᶜ D) ^op)
×ᶜ-op .F₀ x    = x
×ᶜ-op .F₁ f    = f
×ᶜ-op .F-id    = refl
×ᶜ-op .F-∘ _ _ = refl

F×-interchange
  : {F : Functor C D} {G : Functor C' D'}
  → {H : Functor B C} {K : Functor B' C'}
  → ((F F∘ H) F× (G F∘ K)) ≅ⁿ (F F× G) F∘ (H F× K)
F×-interchange = trivial-isoⁿ!

module ProdIso {o ℓ} {C : Precategory o ℓ} (Cart : Cartesian-category C) where
  open Cartesian-category Cart
  open Monoidal-category (Cartesian-monoidal Cart)
  private
    module C = Cr C
    module ip {n} (F : C.Ob ^ n) =
      Indexed-product (Cartesian→standard-finite-products terminal products F)

  _⊗Iso_ : {A A' B B' : C.Ob} → A C.≅ A' → B C.≅ B' → (A ⊗ B) C.≅ (A' ⊗ B')
  iA ⊗Iso iB = F-map-iso ×-functor (iA ,Iso iB)

  ΠIso : ∀ {n} {F1 F2 : C.Ob ^ n} → (∀ i → F1 i ≅ F2 i) → ip.ΠF F1 ≅ ip.ΠF F2
  ΠIso {zero} H≅        = id-iso
  ΠIso {suc zero} H≅    = H≅ fzero
  ΠIso {suc (suc n)} H≅ = H≅ fzero ⊗Iso ΠIso (H≅ ⊙ fsuc)

  Π-cons : ∀ {m} (F : C.Ob ^ suc m) → ip.ΠF F ≅ head F ⊗ ip.ΠF (tail F)
  Π-cons {zero}  F = ρ≅
  Π-cons {suc m} F = id-iso

  Π-++ : ∀ {m n} (F1 : C.Ob ^ m) (F2 : C.Ob ^ n) → ip.ΠF F1 ⊗ ip.ΠF F2 ≅ ip.ΠF (F1 ++ F2)
  Π-++ {zero} F1 F2 =
    λ≅ Iso⁻¹ ∙Iso path→iso (ap ip.ΠF (++-split 0 (F1 ++ F2)))
  Π-++ {suc m} F1 F2 =
    ip.ΠF F1 ⊗ ip.ΠF F2                  ≅⟨ F-map-iso (Bifunctor.Left -⊗- (ip.ΠF F2)) (Π-cons F1) ∙Iso α≅ ⟩
    head F1 ⊗ ip.ΠF (tail F1) ⊗ ip.ΠF F2 ≅⟨ F-map-iso (Bifunctor.Right -⊗- (head F1)) (Π-++ (tail F1) F2 ∙Iso path→iso (ap ip.ΠF (sym (++-tail F1 F2)))) ⟩
    head F1 ⊗ ip.ΠF (tail (F1 ++ F2))    ≅˘⟨ Π-cons (F1 ++ F2) ⟩
    ip.ΠF (F1 ++ F2)                     ≅∎
