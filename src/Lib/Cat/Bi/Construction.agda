open import Lib.Cat.Product

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Solver
open import Cat.Functor.Base
open import Cat.Functor.Compose hiding (_◆_)
open import Cat.Functor.Constant
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Naturality
open import Cat.Instances.Product

open import Lib.Cat.Bi.Lax-transfor
open import Lib.Cat.Bi.Modification

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Lib.Cat.Bi.Construction where

open Functor
open _=>_ hiding (op)

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
  _^co .Pb.unitor-l = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta           = λ←
    ni .make-natural-iso.inv           = λ→
    ni .make-natural-iso.eta∘inv _     = λ≅ .invl
    ni .make-natural-iso.inv∘eta _     = λ≅ .invr
    ni .make-natural-iso.natural _ _ _ = λ←nat _
  _^co .Pb.unitor-r = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta           = ρ←
    ni .make-natural-iso.inv           = ρ→
    ni .make-natural-iso.eta∘inv _     = ρ≅ .invl
    ni .make-natural-iso.inv∘eta _     = ρ≅ .invr
    ni .make-natural-iso.natural _ _ _ = ρ←nat _
  _^co .Pb.associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta           = associator.from .η
    ni .make-natural-iso.inv           = associator.to .η
    ni .make-natural-iso.eta∘inv _     = α≅ .invl
    ni .make-natural-iso.inv∘eta _     = α≅ .invr
    ni .make-natural-iso.natural _ _ _ = α←nat _ _ _
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
      B-compose .F₀ ((F , F-mor) , (G , G-mor)) = F ⊗ G , H-∘ G F G-mor F-mor
      B-compose .F₁                             = ⊗.₁
      B-compose .F-id                           = ⊗.F-id
      B-compose .F-∘                            = ⊗.F-∘

      B-assoc : Associator-for B[_,_] B-compose
      B-assoc = to-natural-iso ni where
        ni : make-natural-iso _ _
        ni .make-natural-iso.eta _         = α≅ .to
        ni .make-natural-iso.inv _         = α≅ .from
        ni .make-natural-iso.eta∘inv _     = α≅ .invl
        ni .make-natural-iso.inv∘eta _     = α≅ .invr
        ni .make-natural-iso.natural _ _ _ = sym $ α→nat _ _ _

      pb : Prebicategory _ _ _
      pb .Pb.Ob = Ob'
      pb .Pb.Hom = B[_,_]
      pb .Pb.id = B-id
      pb .Pb.compose = B-compose
      pb .Pb.unitor-r = to-natural-iso ni where
        ni : make-natural-iso _ _
        ni .make-natural-iso.eta _           = ρ≅ .to
        ni .make-natural-iso.inv _           = ρ≅ .from
        ni .make-natural-iso.eta∘inv (f , _) = ρ≅ .invl
        ni .make-natural-iso.inv∘eta (f , _) = ρ≅ .invr
        ni .make-natural-iso.natural _ _ _   = sym $ ρ→nat _
      pb .Pb.unitor-l = to-natural-iso ni where
        ni : make-natural-iso _ _
        ni .make-natural-iso.eta _           = λ≅ .to
        ni .make-natural-iso.inv _           = λ≅ .from
        ni .make-natural-iso.eta∘inv (f , _) = λ≅ .invl
        ni .make-natural-iso.inv∘eta (f , _) = λ≅ .invr
        ni .make-natural-iso.natural _ _ _   = sym $ λ→nat _
      pb .Pb.associator = B-assoc
      pb .Pb.triangle (f , _) (g , _) = triangle f g
      pb .Pb.pentagon (f , _) (g , _) (h , _) (i , _) = pentagon f g h i


module _ {o h ℓ} {C : Prebicategory o h ℓ} where
  open Prebicategory C
  private
    module C = Br C
    module CH = C.Hom
    module Cat = Prebicategory (Cat h ℓ)

  module _ (X : Ob) where

    Hom-from-bi₁ : ∀ {A B} → Functor (Hom A B) Cat[ Hom X A , Hom X B ]
    Hom-from-bi₁ .F₀ f    = compose F∘ Cat⟨ Const f , Id ⟩
    Hom-from-bi₁ .F₁ α    = compose ▸ (constⁿ α nt, idnt)
    Hom-from-bi₁ .F-id    = ext λ _ → ⊗.F-id
    Hom-from-bi₁ .F-∘ f g = ext λ _ → C.◀-distribl

    Hom-from-bi : Lax-functor C (Cat h ℓ)
    Hom-from-bi = lf where
      open Lax-functor
      open Cr._≅_
      open Cr.Inverses

      Hom-compositor : ∀ {A B C} → Cat.compose F∘ (Hom-from-bi₁ {B} {C} F× Hom-from-bi₁ {A} {B}) => Hom-from-bi₁ F∘ compose
      Hom-compositor .η (f , g) .η x              = α← (f , g , x)
      Hom-compositor .η (f , g) .is-natural _ _ h =
        C.▶-assoc .from .is-natural _ _ _
      Hom-compositor .is-natural _ _ (α , β) = ext λ h →
        α← _ ∘ (_ ▶ (β ◀ _)) ∘ (α ◀ _) ≡⟨ CH.refl⟩∘⟨ C.⊗.collapse (CH.idl _ ,ₚ CH.idr _) ⟩
        α← _ ∘ (α ◆ (β ◀ _))           ≡⟨ α←nat _ _ _ ⟩
        ((α ◆ β) ◀ _) ∘ α← _           ∎

      Hom-unitor : ∀ {A} → Cat.id => Hom-from-bi₁ {A} {A} .F₀ id
      Hom-unitor .η                = λ→
      Hom-unitor .is-natural _ _ α = λ→nat α

      lf : Lax-functor _ _
      lf .P₀            = Hom X
      lf .P₁            = Hom-from-bi₁
      lf .compositor    = Hom-compositor
      lf .unitor        = Hom-unitor
      lf .hexagon f g h = ext λ _ → bicat! C
      lf .right-unit f  = ext λ _ → bicat! C
      lf .left-unit f   = ext λ _ → bicat! C


module _ {o o' h h' ℓ ℓ'} {B : Prebicategory o h ℓ} {C : Prebicategory o' h' ℓ'} where
  module C  = Br C
  module CH = C.Hom

  Lax[_,_] : Lax-functor B C → Lax-functor B C → Precategory _ _
  Lax[ F , G ] = cat where
    open Precategory
    cat : Precategory _ _
    cat .Ob          = F =>ₗ G
    cat .Hom         = Modification
    cat .Hom-set _ _ = Mod-is-set
    cat .id          = idmd
    cat ._∘_         = _∘md_
    cat .idr _       = ext λ _ → CH.idr _
    cat .idl _       = ext λ _ → CH.idl _
    cat .assoc _ _ _ = ext λ _ → CH.assoc _ _ _

  Lax-compose
    : {F G H : Lax-functor B C} → Functor (Lax[ G , H ] ×ᶜ Lax[ F , G ]) Lax[ F , H ]
  Lax-compose .F₀ (α , β) = α ∘lx β
  Lax-compose .F₁ (f , g) = let foo = _◆md_ in {!!}
  Lax-compose .F-id       = {!!} -- ext λ _ → C.⊗.F-id
  Lax-compose .F-∘ f g    = {!!} -- ext λ _ → C.⊗.F-∘ _ _

  -- Lax : Prebicategory (o₁ ⊔ h₁ ⊔ ℓ₁ ⊔ o₂ ⊔ h₂ ⊔ ℓ₂) (o₁ ⊔ h₁ ⊔ ℓ₁ ⊔ h₂ ⊔ ℓ₂) (o₁ ⊔ h₁ ⊔ ℓ₂)
  -- Lax .Prebicategory.Ob         = Lax-functor B C
  -- Lax .Prebicategory.Hom        = Lax[_,_]
  -- Lax .Prebicategory.id         = idlx
  -- Lax .Prebicategory.compose    = Lax-compose
  -- Lax .Prebicategory.unitor-l   = {!!}
  -- Lax .Prebicategory.unitor-r   = {!!}
  -- Lax .Prebicategory.associator = {!!}
  -- Lax .Prebicategory.triangle   = {!!}
  -- Lax .Prebicategory.pentagon   = {!!}
