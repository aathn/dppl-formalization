module Lib.Cat.Bi where

open import Cat.Prelude

open import Cat.Bi.Base
open import Cat.Functor.Base
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Naturality
open import Cat.Instances.Product
import Cat.Morphism as Mor

-- We define sub-bicategories whose hom-categories are full
-- subcategories.

open Functor
open _=>_

module _ {o ℓ ℓ' ℓx ℓp} (BC : Prebicategory o ℓ ℓ') (O : Prebicategory.Ob BC → Type ℓx) where
  module BC = Prebicategory BC

  Ob' : Type _
  Ob' = Σ BC.Ob O

  B'[_,_] : Ob' → Ob' → Precategory _ _
  B'[ A , B ] = BC.Hom (A .fst) (B .fst)

  Birestrict
    : (H : (A B : Ob') → ⌞ B'[ A , B ] ⌟ → Type ℓp)
    → (H-id : {A : Ob'} → H A A BC.id)
    → (H-∘
        : {A B C : Ob'} (F : ⌞ B'[ A , B ] ⌟) (G : ⌞ B'[ B , C ] ⌟)
        → H A B F → H B C G → H A C (BC.compose.₀ (G , F)))
    → Prebicategory (o ⊔ ℓx) (ℓ ⊔ ℓp) ℓ'
  Birestrict H H-id H-∘ = pb where
    open Prebicategory
    open make-natural-iso
    open Mor._≅_
    open Mor.Inverses

    B[_,_] : Ob' → Ob' → Precategory _ _
    B[ A , B ] = Restrict {C = B'[ A , B ]} (H A B)

    B-id : {C : Ob'} → ⌞ B[ C , C ] ⌟
    B-id = BC.id , H-id

    B-compose : {A B C : Ob'} → Functor (B[ B , C ] ×ᶜ B[ A , B ]) B[ A , C ]
    B-compose = record
      { F₀   = λ ((F , F-mor) , (G , G-mor)) → BC.compose.₀ (F , G) , H-∘ G F G-mor F-mor
      ; F₁   = BC.compose.₁
      ; F-id = BC.compose.F-id
      ; F-∘  = BC.compose.F-∘
      }

    B-assoc : Associator-for B[_,_] B-compose
    B-assoc = to-natural-iso ni where
      ni : make-natural-iso _ _
      ni .eta _ = BC.associator .to .η _
      ni .inv _ = BC.associator .from .η _
      ni .eta∘inv ((f , _) , (g , _) , (h , _)) =
        BC.associator .inverses .invl ηₚ (f , g , h)
      ni .inv∘eta ((f , _) , (g , _) , (h , _)) =
        BC.associator .inverses .invr ηₚ (f , g , h)
      ni .natural _ _ α = sym $ BC.associator .to .is-natural _ _ α

    pb : Prebicategory _ _ _
    pb .Ob = Ob'
    pb .Hom = B[_,_]
    pb .id = B-id
    pb .compose = B-compose
    pb .unitor-r = to-natural-iso ni where
      ni : make-natural-iso _ _
      ni .eta _ = BC.unitor-r .to .η _
      ni .inv _ = BC.unitor-r .from .η _
      ni .eta∘inv (f , _) = BC.unitor-r .inverses .invl ηₚ f
      ni .inv∘eta (f , _) = BC.unitor-r .inverses .invr ηₚ f
      ni .natural _ _ α = sym $ BC.unitor-r .to .is-natural _ _ α
    pb .unitor-l = to-natural-iso ni where
      ni : make-natural-iso _ _
      ni .eta _ = BC.unitor-l .to .η _
      ni .inv _ = BC.unitor-l .from .η _
      ni .eta∘inv (f , _) = BC.unitor-l .inverses .invl ηₚ f
      ni .inv∘eta (f , _) = BC.unitor-l .inverses .invr ηₚ f
      ni .natural _ _ α = sym $ BC.unitor-l .to .is-natural _ _ α
    pb .associator = B-assoc
    pb .triangle (f , _) (g , _) = BC.triangle f g
    pb .pentagon (f , _) (g , _) (h , _) (i , _) = BC.pentagon f g h i
