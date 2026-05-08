open import Cat.Diagram.Product.Indexed
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Cartesian
open import Cat.Prelude

open import Data.Fin.Base
open import Data.Sum.Base

open import Lib.Data.Vector
open import Lib.Data.Fin

import Cat.Morphism as Cm

module Lib.Cat.Product where

open Cm._≅_
open Cm.Inverses

private variable
  o h : Level
  C D : Precategory o h

_,Iso_
  : {A A' : ⌞ C ⌟} {B B' : ⌞ D ⌟} → Cm._≅_ C A A' → Cm._≅_ D B B'
  → Cm._≅_ (C ×ᶜ D) (A , B) (A' , B')
(iA ,Iso iB) .to             = iA .to , iB .to
(iA ,Iso iB) .from           = iA .from , iB .from
(iA ,Iso iB) .inverses .invl = iA .invl ,ₚ iB .invl
(iA ,Iso iB) .inverses .invr = iA .invr ,ₚ iB .invr

module ProdIso {o ℓ} {C : Precategory o ℓ} (Cart : Cartesian-category C) where
  open Cartesian-category Cart

  _⊗Iso_ : {A A' B B' : Ob} → A ≅ A' → B ≅ B' → (A ⊗₀ B) ≅ (A' ⊗₀ B')
  iA ⊗Iso iB = F-map-iso ×-functor (iA ,Iso iB)

  module IndexedProdIso (ip : ∀ {n} → has-products-indexed-by C (Fin n)) where

    private module ip {n} (F : Ob ^ n) = Indexed-product (ip F)

    ΠIso : ∀ {n} {F1 F2 : Ob ^ n} → (∀ i → F1 i ≅ F2 i) → ip.ΠF F1 ≅ ip.ΠF F2
    ΠIso H≅ .to       = ip.tuple _ λ i → H≅ i .to ∘ ip.π _ i
    ΠIso H≅ .from     = ip.tuple _ λ i → H≅ i .from ∘ ip.π _ i
    ΠIso H≅ .inverses .invl = ip.unique₂ _ λ i →
         extendl (ip.commute _) ∙ cdr (ip.commute _)
      ∙∙ cancell (H≅ i .invl) ∙∙ sym (idr _)
    ΠIso H≅ .inverses .invr = ip.unique₂ _ λ i →
         extendl (ip.commute _) ∙ cdr (ip.commute _)
      ∙∙ cancell (H≅ i .invr) ∙∙ sym (idr _)

    Π-0 : {F : Ob ^ 0} → ip.ΠF F ≅ top
    Π-0 .to             = !
    Π-0 .from           = ip.tuple _ λ ()
    Π-0 .inverses .invl = !-unique₂ _ _
    Π-0 .inverses .invr = ip.unique₂ _ λ ()

    Π-1 : {F : Ob ^ 1} → ip.ΠF F ≅ head F
    Π-1 .to             = ip.π _ _
    Π-1 .from           = ip.tuple _ $ Fin-cases id λ ()
    Π-1 .inverses .invl = ip.commute _
    Π-1 .inverses .invr =
      ip.unique₂ _ (Fin-cases (cancell (ip.commute _) ∙ sym (idr _)) λ ())

    module _ {m n} (F1 : Ob ^ m) (F2 : Ob ^ n) where

      open is-indexed-product

      is-ip-⊗-Π
        : is-indexed-product C Fin[ F1 , F2 ]
          Fin[ (λ i → ip.π _ i ∘ π₁) , (λ i → ip.π _ i ∘ π₂) ]
      is-ip-⊗-Π .tuple f         = ⟨ ip.tuple _ (f ⊙ inl) , ip.tuple _ (f ⊙ inr) ⟩
      is-ip-⊗-Π .commute {inl x} = pullr π₁∘⟨⟩ ∙ ip.commute _
      is-ip-⊗-Π .commute {inr x} = pullr π₂∘⟨⟩ ∙ ip.commute _
      is-ip-⊗-Π .unique f p      = ⟨⟩-unique
        (ip.unique _ _ λ i → assoc _ _ _ ∙ p (inl i))
        (ip.unique _ _ λ i → assoc _ _ _ ∙ p (inr i))

      Π-++ : ip.ΠF (F1 ++ F2) ≅ (ip.ΠF F1 ⊗₀ ip.ΠF F2)
      Π-++ = is-indexed-product→iso C
        (Indexed-product.has-is-ip
          (Indexed-product-≃ _ (Fin-+-≃ m e⁻¹) (ip (F1 ++ F2))))
        is-ip-⊗-Π

    Π-cons : ∀ {n} (F : Ob ^ (suc n)) → ip.ΠF F ≅ (head F ⊗₀ ip.ΠF (tail F))
    Π-cons F =
           path→iso (ap ip.ΠF (sym (++-singleton ∙ ∷-head-tail F)))
      ∙Iso Π-++ {1} (make (head F)) (tail F)
      ∙Iso (Π-1 ⊗Iso id-iso)
