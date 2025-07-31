module Lib.Cat.Bi where

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Naturality
open import Cat.Instances.Product
import Cat.Reasoning as Cr

-- We define subcategories of Cat, whose hom-categories are
-- full subcategories of Cat[ A , B ].

module _
  {ℓx ℓp} o ℓ (O : Precategory o ℓ → Type ℓx)
  (H : (A B : Σ _ O) → Functor (A .fst) (B .fst) → Type ℓp)
  (H-id : {A : Σ _ O} → H A A Id)
  (H-∘
    : {A B C : Σ _ O} (F : Functor (A .fst) (B .fst)) (G : Functor (B .fst) (C .fst))
    → H A B F → H B C G → H A C (G F∘ F))
  where

  Birestrict : Prebicategory (lsuc o ⊔ lsuc ℓ ⊔ ℓx) (o ⊔ ℓ ⊔ ℓp) (o ⊔ ℓ)
  Birestrict = pb where
    open Prebicategory
    open Functor
    open make-natural-iso

    B[_,_] : (A B : Σ _ O) → Precategory _ _
    B[_,_] A B = Restrict {C = Cat[ A .fst , B .fst ]} (H A B)

    B-id : {C : Σ _ O} → ⌞ B[ C , C ] ⌟
    B-id = Id , H-id

    B-compose : {A B C : Σ _ O} → Functor (B[ B , C ] ×ᶜ B[ A , B ]) B[ A , C ]
    B-compose = record
      { F₀   = λ ((F , F-mor) , (G , G-mor)) → F F∘ G , H-∘ G F G-mor F-mor
      ; F₁   = F∘-functor .F₁
      ; F-id = F∘-functor .F-id
      ; F-∘  = F∘-functor .F-∘
      }

    B-assoc : Associator-for B[_,_] B-compose
    B-assoc {D = D , _} = to-natural-iso ni where
      module D = Cr D
      ni : make-natural-iso {D = B[ _ , _ ]} _ _
      ni .eta x = NT (λ _ → D.id) λ _ _ _ → D.id-comm-sym
      ni .inv x = NT (λ _ → D.id) λ _ _ _ → D.id-comm-sym
      ni .eta∘inv x = ext λ _ → D.idl _
      ni .inv∘eta x = ext λ _ → D.idl _
      ni .natural x y f = ext λ _ →
        D.idr _ ∙∙ D.pushl (y .fst .fst .F-∘ _ _) ∙∙ D.introl refl

    pb : Prebicategory _ _ _
    pb .Ob = Σ[ C ∈ Precategory o ℓ ] O C
    pb .Hom = B[_,_]
    pb .id = B-id
    pb .compose = B-compose
    pb .unitor-r {A = A , _} {B , _} = to-natural-iso ni where
      module B = Cr B
      ni : make-natural-iso {D = B[ _ , _ ]} _ _
      ni .eta x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
      ni .inv x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
      ni .eta∘inv x = ext λ _ → B.idl _
      ni .inv∘eta x = ext λ _ → B.idl _
      ni .natural x y f =
        ext λ _ → B.idr _ ∙ ap (B._∘ _) (y .fst .F-id)
    pb .unitor-l {A = A , _} {B , _} = to-natural-iso ni where
      module B = Cr B
      ni : make-natural-iso {D = B[ _ , _ ]} _ _
      ni .eta x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
      ni .inv x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
      ni .eta∘inv x = ext λ _ → B.idl _
      ni .inv∘eta x = ext λ _ → B.idl _
      ni .natural x y f = ext λ _ → B.idr _ ∙ B.id-comm
    pb .associator = B-assoc
    pb .triangle {C = C , _} f g = ext λ _ → Cr.idr C _
    pb .pentagon {E = E , _} (f , _) (g , _) (h , _) (i , _) = ext λ _ → ap₂ E._∘_
      (E.eliml (ap (f .F₁) (ap (g .F₁) (h .F-id)) ∙∙ ap (f .F₁) (g .F-id) ∙∙ f .F-id))
      (E.elimr (E.eliml (f .F-id)))
      where module E = Cr E
