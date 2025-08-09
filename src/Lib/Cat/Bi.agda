module Lib.Cat.Bi where

open import Cat.Prelude

open import Cat.Bi.Base
open import Cat.Functor.Base
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Naturality
open import Cat.Instances.Discrete
open import Cat.Instances.Product
import Cat.Morphism as Mor

open Functor
open _=>_
open Prebicategory

module _ {o ℓ ℓ' ℓx ℓp} (BC : Prebicategory o ℓ ℓ') (O : Ob BC → Type ℓx) where
  module BC = Prebicategory BC

  -- We define sub-bicategories whose hom-categories are full
  -- subcategories.

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
    B-assoc = to-natural-iso record
      { eta = λ _ → BC.associator .to .η _
      ; inv = λ _ → BC.associator .from .η _
      ; eta∘inv = λ ((f , _) , (g , _) , (h , _)) →
          BC.associator .inverses .invl ηₚ (f , g , h)
      ; inv∘eta = λ ((f , _) , (g , _) , (h , _)) →
          BC.associator .inverses .invr ηₚ (f , g , h)
      ; natural = λ _ _ α → sym $ BC.associator .to .is-natural _ _ α
      }

    pb : Prebicategory _ _ _
    pb .Ob = Ob'
    pb .Hom = B[_,_]
    pb .id = B-id
    pb .compose = B-compose
    pb .unitor-r = to-natural-iso record
      { eta = λ _ → BC.unitor-r .to .η _
      ; inv = λ _ → BC.unitor-r .from .η _
      ; eta∘inv = λ (f , _) → BC.unitor-r .inverses .invl ηₚ f
      ; inv∘eta = λ (f , _) → BC.unitor-r .inverses .invr ηₚ f
      ; natural = λ _ _ α → sym $ BC.unitor-r .to .is-natural _ _ α
      }
    pb .unitor-l = to-natural-iso record
      { eta = λ _ → BC.unitor-l .to .η _
      ; inv = λ _ → BC.unitor-l .from .η _
      ; eta∘inv = λ (f , _) → BC.unitor-l .inverses .invl ηₚ f
      ; inv∘eta = λ (f , _) → BC.unitor-l .inverses .invr ηₚ f
      ; natural = λ _ _ α → sym $ BC.unitor-l .to .is-natural _ _ α
      }
    pb .associator = B-assoc
    pb .triangle (f , _) (g , _) = BC.triangle f g
    pb .pentagon (f , _) (g , _) (h , _) (i , _) = BC.pentagon f g h i

cat→bicat : ∀ {o ℓ} → Precategory o ℓ → Prebicategory o ℓ ℓ
cat→bicat C = pb where
  module C = Precategory C

  HomCat[_,_] : C.Ob → C.Ob → Precategory _ _
  HomCat[ a , b ] = Disc' (el! (C.Hom a b))

  Hom-compose : {a b c : C.Ob} → Functor (HomCat[ b , c ] ×ᶜ HomCat[ a , b ]) HomCat[ a , c ]
  Hom-compose = record
    { F₀   = λ (f , g) → f C.∘ g
    ; F₁   = λ (p , q) → ap₂ C._∘_ p q
    ; F-id = refl
    ; F-∘  = λ _ _ → C.Hom-set _ _ _ _ _ _
    }

  pb : Prebicategory _ _ _
  pb .Ob = C.Ob
  pb .Hom = HomCat[_,_]
  pb .id = C.id
  pb .compose = Hom-compose
  pb .unitor-l = to-natural-iso record
    { eta = sym ⊙ C.idl
    ; inv = C.idl
    ; eta∘inv = λ _ → C.Hom-set _ _ _ _ _ _
    ; inv∘eta = λ _ → C.Hom-set _ _ _ _ _ _
    ; natural = λ _ _ _ → C.Hom-set _ _ _ _ _ _
    }
  pb .unitor-r = to-natural-iso record
    { eta = sym ⊙ C.idr
    ; inv = C.idr
    ; eta∘inv = λ _ → C.Hom-set _ _ _ _ _ _
    ; inv∘eta = λ _ → C.Hom-set _ _ _ _ _ _
    ; natural = λ _ _ _ → C.Hom-set _ _ _ _ _ _
    }
  pb .associator = to-natural-iso record
    { eta = λ _ → sym $ C.assoc _ _ _
    ; inv = λ _ → C.assoc _ _ _
    ; eta∘inv = λ _ → C.Hom-set _ _ _ _ _ _
    ; inv∘eta = λ _ → C.Hom-set _ _ _ _ _ _
    ; natural = λ _ _ _ → C.Hom-set _ _ _ _ _ _
    }
  pb .triangle _ _ = C.Hom-set _ _ _ _ _ _
  pb .pentagon _ _ _ _ = C.Hom-set _ _ _ _ _ _
