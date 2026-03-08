module Lib.Cat.Bi.Construction where

open import Lib.Cat.Product
import Lib.Cat.Bi.Reasoning as Br
import Lib.Cat.Bi.Solver as Solver

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Functor.Base
open import Cat.Functor.Compose hiding (_◆_)
open import Cat.Functor.Constant
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Naturality
open import Cat.Instances.Discrete
open import Cat.Instances.Product
import Cat.Reasoning as Cr

open Functor
open _=>_ hiding (op)

cat→bicat : ∀ {o ℓ} → Precategory o ℓ → Prebicategory o ℓ ℓ
cat→bicat C = pb where
  module C = Precategory C
  open Prebicategory

  HomCat[_,_] : C.Ob → C.Ob → Precategory _ _
  HomCat[ a , b ] = Disc' (el (C.Hom a b) (C.Hom-set a b))

  Hom-compose : {a b c : C.Ob} → Functor (HomCat[ b , c ] ×ᶜ HomCat[ a , b ]) HomCat[ a , c ]
  Hom-compose = record
    { F₀   = λ (f , g) → f C.∘ g
    ; F₁   = λ (p , q) → ap₂ C._∘_ p q
    ; F-id = refl
    ; F-∘  = λ _ _ → C.Hom-set _ _ _ _ _ _
    }

  pb : Prebicategory _ _ _
  pb .Ob       = C.Ob
  pb .Hom      = HomCat[_,_]
  pb .id       = C.id
  pb .compose  = Hom-compose
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
  pb .triangle _ _     = C.Hom-set _ _ _ _ _ _
  pb .pentagon _ _ _ _ = C.Hom-set _ _ _ _ _ _


module _ {o h ℓ} (C : Prebicategory o h ℓ) where
  open Br C
  open Hom hiding (Ob ; Hom ; id ; _∘_)
  private
    module Pb = Prebicategory

  open Cr._≅_
  open Cr.Inverses

  infixl 60 _^co
  _^co : Prebicategory o h ℓ
  _^co .Pb.Ob       = Ob
  _^co .Pb.Hom x y  = Hom x y ^op
  _^co .Pb.id       = id
  _^co .Pb.compose  = op compose F∘ ×ᶜ-op
  _^co .Pb.unitor-l = to-natural-iso record
    { eta = λ←
    ; inv = λ→
    ; eta∘inv = λ _ → λ≅ .invl
    ; inv∘eta = λ _ → λ≅ .invr
    ; natural = λ _ _ _ → λ←nat _
    }
  _^co .Pb.unitor-r = to-natural-iso record
    { eta = ρ←
    ; inv = ρ→
    ; eta∘inv = λ _ → ρ≅ .invl
    ; inv∘eta = λ _ → ρ≅ .invr
    ; natural = λ _ _ _ → ρ←nat _
    }
  _^co .Pb.associator = to-natural-iso record
    { eta = associator.from .η
    ; inv = associator.to .η
    ; eta∘inv = λ _ → α≅ .invl
    ; inv∘eta = λ _ → α≅ .invr
    ; natural = λ _ _ _ → α←nat _ _ _
    }
  _^co .Pb.triangle f g = inverse-unique refl refl
    (α≅ Iso⁻¹ ∙Iso ◀.F-map-iso (ρ≅ Iso⁻¹))
    (▶.F-map-iso (λ≅ Iso⁻¹))
    (triangle f g)
  _^co .Pb.pentagon _ _ _ _ = sym (assoc _ _ _) ∙ pentagon-α→


  module _ {ℓx ℓp} (O : Ob → Type ℓx) where
    -- We define sub-bicategories whose hom-categories are full
    -- subcategories.

    Ob' : Type _
    Ob' = Σ Ob O

    B'[_,_] : Ob' → Ob' → Precategory _ _
    B'[ A , B ] = Hom (A .fst) (B .fst)

    Birestrict
      : (H : (A B : Ob') → ⌞ B'[ A , B ] ⌟ → Type ℓp)
      → (H-id : {A : Ob'} → H A A id)
      → (H-∘
          : {A B C : Ob'} (F : ⌞ B'[ A , B ] ⌟) (G : ⌞ B'[ B , C ] ⌟)
          → H A B F → H B C G → H A C (G ⊗ F))
      → Prebicategory (o ⊔ ℓx) (h ⊔ ℓp) ℓ
    Birestrict H H-id H-∘ = pb where

      B[_,_] : Ob' → Ob' → Precategory _ _
      B[ A , B ] = Restrict {C = B'[ A , B ]} (H A B)

      B-id : {C : Ob'} → ⌞ B[ C , C ] ⌟
      B-id = id , H-id

      B-compose : {A B C : Ob'} → Functor (B[ B , C ] ×ᶜ B[ A , B ]) B[ A , C ]
      B-compose = record
        { F₀   = λ ((F , F-mor) , (G , G-mor)) → F ⊗ G , H-∘ G F G-mor F-mor
        ; F₁   = ⊗.₁
        ; F-id = ⊗.F-id
        ; F-∘  = ⊗.F-∘
        }

      B-assoc : Associator-for B[_,_] B-compose
      B-assoc = to-natural-iso record
        { eta = λ _ → α≅ .to
        ; inv = λ _ → α≅ .from
        ; eta∘inv = λ _ → α≅ .invl
        ; inv∘eta = λ _ → α≅ .invr
        ; natural = λ _ _ _ → sym $ α→nat _ _ _
        }

      pb : Prebicategory _ _ _
      pb .Pb.Ob = Ob'
      pb .Pb.Hom = B[_,_]
      pb .Pb.id = B-id
      pb .Pb.compose = B-compose
      pb .Pb.unitor-r = to-natural-iso record
        { eta = λ _ → ρ≅ .to
        ; inv = λ _ → ρ≅ .from
        ; eta∘inv = λ (f , _) → ρ≅ .invl
        ; inv∘eta = λ (f , _) → ρ≅ .invr
        ; natural = λ _ _ _ → sym $ ρ→nat _
        }
      pb .Pb.unitor-l = to-natural-iso record
        { eta = λ _ → λ≅ .to
        ; inv = λ _ → λ≅ .from
        ; eta∘inv = λ (f , _) → λ≅ .invl
        ; inv∘eta = λ (f , _) → λ≅ .invr
        ; natural = λ _ _ _ → sym $ λ→nat _
        }
      pb .Pb.associator = B-assoc
      pb .Pb.triangle (f , _) (g , _) = triangle f g
      pb .Pb.pentagon (f , _) (g , _) (h , _) (i , _) = pentagon f g h i


module _ {o h ℓ} {C : Prebicategory o h ℓ} where
  open Br C
  open Hom hiding (Ob ; Hom ; id ; _∘_)
  open Solver C
  private
    module Cat = Prebicategory (Cat h ℓ)

  module _ (X : Ob) where
    open Lax-functor
    open Cr._≅_
    open Cr.Inverses

    Hom-from-bi₁ : ∀ {A B} → Functor (Hom A B) Cat[ Hom X A , Hom X B ]
    Hom-from-bi₁ .F₀ f    = compose F∘ Cat⟨ Const f , Id ⟩
    Hom-from-bi₁ .F₁ α    = compose ▸ (constⁿ α nt, idnt)
    Hom-from-bi₁ .F-id    = ext λ _ → ⊗.F-id
    Hom-from-bi₁ .F-∘ f g = ext λ _ → ◀-distribl

    Hom-from-bi : Lax-functor C (Cat h ℓ)
    Hom-from-bi = lf where

      Hom-compositor : ∀ {A B C} → Cat.compose F∘ (Hom-from-bi₁ {B} {C} F× Hom-from-bi₁ {A} {B}) => Hom-from-bi₁ F∘ compose
      Hom-compositor .η (f , g) .η x              = α← f g x
      Hom-compositor .η (f , g) .is-natural _ _ h =
        ▶-assoc .from .is-natural _ _ _
      Hom-compositor .is-natural _ _ (α , β) = ext λ h →
        α← _ _ _ ∘ (_ ▶ (β ◀ _)) ∘ (α ◀ _) ≡⟨ refl⟩∘⟨ ⊗.collapse (ap₂ _,_ (idl _) (idr _)) ⟩
        α← _ _ _ ∘ (α ◆ (β ◀ _))           ≡⟨ α←nat _ _ _ ⟩
        ((α ◆ β) ◀ _) ∘ α← _ _ _           ∎

      Hom-unitor : ∀ {A} → Cat.id => Hom-from-bi₁ {A} {A} .F₀ id
      Hom-unitor .η                = λ→
      Hom-unitor .is-natural _ _ α = λ→nat α

      lf : Lax-functor _ _
      lf .P₀            = Hom X
      lf .P₁            = Hom-from-bi₁
      lf .compositor    = Hom-compositor
      lf .unitor        = Hom-unitor
      lf .hexagon f g h = ext λ u → solve
        (`α→ _ (g ↑) (h ↑) `◀ u ↑ `∘ `α← _ _ _ `∘ (`id `◆ `id) `∘ `α← _ _ _)
        (`α← _ _ _ `∘ (f ↑ `▶ `α← _ _ _ `∘ `id) `∘ `id) refl
      lf .right-unit f = ext λ h → solve
        (`ρ← (f ↑) `◀ h ↑ `∘ `α← _ _ _ `∘ _ `▶ `λ→ _ `∘ `id) `id refl
      lf .left-unit f = ext λ h → solve
        (`λ← (f ↑) `◀ h ↑ `∘ `α← _ _ _ `∘ (`id `◆ `id) `∘ `λ→ _) `id refl
