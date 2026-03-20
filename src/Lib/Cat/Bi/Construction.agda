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

open import Lib.Cat.Bi.Lax-functor
open import Lib.Cat.Bi.Lax-transfor
open import Lib.Cat.Bi.Modification

import Cat.Functor.Bifunctor as Bi
import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Lib.Cat.Bi.Construction where

open Cr.is-invertible hiding (op)
open Pseudofunctor
open Cr.Inverses
open Lax-functor
open Functor
open Cr._≅_
open _=>_ hiding (op)

private
  module Pb = Prebicategory
  variable
    o o' h h' ℓ ℓ' : Level
    B C : Prebicategory o h ℓ

module _ (C : Prebicategory o h ℓ) where
  open Br C
  open Hom hiding (Ob ; Hom ; id ; _∘_)

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
    ni .make-natural-iso.eta           = α←
    ni .make-natural-iso.inv           = α→
    ni .make-natural-iso.eta∘inv _     = α≅ .invl
    ni .make-natural-iso.inv∘eta _     = α≅ .invr
    ni .make-natural-iso.natural _ _ _ = α←nat _ _ _
  _^co .Pb.triangle f g                = lswizzle (sym triangle-inv) (α≅ .invl)
  _^co .Pb.pentagon _ _ _ _            = sym (assoc _ _ _) ∙ pentagon-α→


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

  module _ (X : Ob) where
    private module Cat = Prebicategory (Cat h ℓ)

    Hom-from-bi₁ : ∀ {A B} → Functor (Hom A B) Cat[ Hom X A , Hom X B ]
    Hom-from-bi₁ .F₀ f    = compose F∘ Cat⟨ Const f , Id ⟩
    Hom-from-bi₁ .F₁ α    = compose ▸ (constⁿ α nt, idnt)
    Hom-from-bi₁ .F-id    = ext λ _ → ⊗.F-id
    Hom-from-bi₁ .F-∘ f g = ext λ _ → ◀-distribl

    Hom-from-bi : Lax-functor C (Cat h ℓ)
    Hom-from-bi = lf where
      Hom-compositor
        : ∀ {A B C}
        → Cat.compose F∘ (Hom-from-bi₁ {B} {C} F× Hom-from-bi₁ {A} {B}) => Hom-from-bi₁ F∘ compose
      Hom-compositor .η (f , g) .η x              = α← (f , g , x)
      Hom-compositor .η (f , g) .is-natural _ _ h = ▶-assoc .from .is-natural _ _ _
      Hom-compositor .is-natural _ _ (α , β) = ext λ h →
        α← _ ∘ (_ ▶ (β ◀ _)) ∘ (α ◀ _) ≡⟨ refl⟩∘⟨ ⊗.collapse (idl _ ,ₚ idr _) ⟩
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


Lax[_,_] : Lax-functor B C → Lax-functor B C → Precategory _ _
Lax[_,_] {C = C} F G = cat where
  open Prebicategory C
  cat : Precategory _ _
  cat .Precategory.Ob          = F =>ₗ G
  cat .Precategory.Hom         = Modification
  cat .Precategory.Hom-set _ _ = Mod-is-set
  cat .Precategory.id          = idmd
  cat .Precategory._∘_         = _∘md_
  cat .Precategory.idr _       = ext λ _ → Hom.idr _
  cat .Precategory.idl _       = ext λ _ → Hom.idl _
  cat .Precategory.assoc _ _ _ = ext λ _ → Hom.assoc _ _ _

co : Pseudofunctor B C → Pseudofunctor (B ^co) (C ^co)
co {B = B} {C = C} F = pf where
  module B  = Br B
  module C  = Br C
  module CH = C.Hom
  module F  = Pf-reasoning F
  pf : Pseudofunctor _ _
  pf .lax .P₀                           = F.P₀
  pf .lax .P₁                           = F.P₁.op
  pf .lax .compositor .η                = F.γ←
  pf .lax .compositor .is-natural _ _ _ = sym $ F.γ←nat _ _
  pf .lax .unitor                       = F.υ←
  pf .lax .hexagon f g h = CH.inverse-unique refl refl
    (F.P₁.F-map-iso B.α≅ CH.∘Iso F.γ≅ CH.∘Iso C.◀.F-map-iso F.γ≅)
    (F.γ≅ CH.∘Iso C.▶.F-map-iso F.γ≅ CH.∘Iso C.α≅)
    (F.hexagon f g h)
  pf .lax .right-unit f = CH.inverse-unique refl refl
    (F.P₁.F-map-iso B.ρ≅ CH.Iso⁻¹ CH.∘Iso F.γ≅ CH.∘Iso C.▶.F-map-iso F.υ≅)
    (C.ρ≅ CH.Iso⁻¹) (F.right-unit f)
  pf .lax .left-unit f  = CH.inverse-unique refl refl
    (F.P₁.F-map-iso B.λ≅ CH.Iso⁻¹ CH.∘Iso F.γ≅ CH.∘Iso C.◀.F-map-iso F.υ≅)
    (C.λ≅ CH.Iso⁻¹) (F.left-unit f)
  pf .unitor-inv .inv                   = F.υ→
  pf .unitor-inv .inverses .invl        = F.unitor-inv .inverses .invl
  pf .unitor-inv .inverses .invr        = F.unitor-inv .inverses .invr
  pf .compositor-inv fg .inv            = F.γ→ fg
  pf .compositor-inv fg .inverses .invl = F.compositor-inv fg .inverses .invl
  pf .compositor-inv fg .inverses .invr = F.compositor-inv fg .inverses .invr


module _ (B : Prebicategory o h ℓ) (C : Prebicategory o' h' ℓ') where
  private module C = Br C

  open Lax-transfor
  open Modification

  Lax : Prebicategory _ _ _
  Lax = pb module Lax where
    compose
      : {F G H : Lax-functor B C}
      → Functor (Lax[ G , H ] ×ᶜ Lax[ F , G ]) Lax[ F , H ]
    compose .F₀ (α , β) = α ∘lx β
    compose .F₁ (f , g) = f ◆md g
    compose .F-id       = ext λ _ → C.⊗.F-id
    compose .F-∘ f g    = ext λ _ → C.⊗.F-∘ _ _

    unitor-l : ∀ {F G} → Id ≅ⁿ Bi.Right (compose {F = F} {G}) idlx
    unitor-l = to-natural-iso ni where
      ni : make-natural-iso _ _
      ni .make-natural-iso.eta x .Γ a        = C.λ→ (σ x a)
      ni .make-natural-iso.eta x .is-natural = bicat! C
      ni .make-natural-iso.inv x .Γ a        = C.λ← (σ x a)
      ni .make-natural-iso.inv x .is-natural = bicat! C
      ni .make-natural-iso.eta∘inv x         = ext λ _ → C.λ≅ .invl
      ni .make-natural-iso.inv∘eta x         = ext λ _ → C.λ≅ .invr
      ni .make-natural-iso.natural _ _ _     = ext λ _ → sym $ C.λ→nat _

    unitor-r : ∀ {F G} → Id ≅ⁿ Bi.Left (compose {G = F} {G}) idlx
    unitor-r = to-natural-iso ni where
      ni : make-natural-iso _ _
      ni .make-natural-iso.eta x .Γ a        = C.ρ→ (σ x a)
      ni .make-natural-iso.eta x .is-natural = bicat! C
      ni .make-natural-iso.inv x .Γ a        = C.ρ← (σ x a)
      ni .make-natural-iso.inv x .is-natural = bicat! C
      ni .make-natural-iso.eta∘inv x         = ext λ _ → C.ρ≅ .invl
      ni .make-natural-iso.inv∘eta x         = ext λ _ → C.ρ≅ .invr
      ni .make-natural-iso.natural _ _ _     = ext λ _ → sym $ C.ρ→nat _

    associator : Associator-for Lax[_,_] compose
    associator = to-natural-iso ni where
      ni : make-natural-iso _ _
      ni .make-natural-iso.eta x .Γ a        = C.α→ _
      ni .make-natural-iso.eta x .is-natural = bicat! C
      ni .make-natural-iso.inv x .Γ a        = C.α← _
      ni .make-natural-iso.inv x .is-natural = bicat! C
      ni .make-natural-iso.eta∘inv x         = ext λ _ → C.α≅ .invl
      ni .make-natural-iso.inv∘eta x         = ext λ _ → C.α≅ .invr
      ni .make-natural-iso.natural _ _ _     = ext λ _ → sym $ C.α→nat _ _ _

    pb : Prebicategory _ _ _
    pb .Pb.Ob               = Lax-functor B C
    pb .Pb.Hom              = Lax[_,_]
    pb .Pb.id               = idlx
    pb .Pb.compose          = compose
    pb .Pb.unitor-l         = unitor-l
    pb .Pb.unitor-r         = unitor-r
    pb .Pb.associator       = associator
    pb .Pb.triangle f g     = ext λ _ → C.triangle (σ f _) (σ g _)
    pb .Pb.pentagon f g h i = ext λ _ → C.pentagon (σ f _) (σ g _) (σ h _) (σ i _)

module _ (B : Prebicategory o h ℓ) (C : Prebicategory o' h' ℓ') where
  private module C = Br C

  Pseudo-oplax : Prebicategory _ _ _
  Pseudo-oplax .Pb.Ob         = Pseudofunctor B C
  Pseudo-oplax .Pb.Hom F G    = Lax[ co F .lax , co G .lax ]
  Pseudo-oplax .Pb.id         = idlx
  Pseudo-oplax .Pb.compose    = Lax.compose (B ^co) (C ^co)
  Pseudo-oplax .Pb.unitor-l   = Lax.unitor-l (B ^co) (C ^co)
  Pseudo-oplax .Pb.unitor-r   = Lax.unitor-r (B ^co) (C ^co)
  Pseudo-oplax .Pb.associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta           = Lax.associator (B ^co) (C ^co) .to .η
    ni .make-natural-iso.inv           = Lax.associator (B ^co) (C ^co) .from .η
    ni .make-natural-iso.eta∘inv _     = ext λ _ → C.α≅ .invl
    ni .make-natural-iso.inv∘eta _     = ext λ _ → C.α≅ .invr
    ni .make-natural-iso.natural _ _ _ = ext λ _ → C.α←nat _ _ _
  Pseudo-oplax .Pb.triangle f g        = ext λ _ →
    C.Hom.lswizzle (sym C.triangle-inv) (C.α≅ .invl)
  Pseudo-oplax .Pb.pentagon f g h i =
    ext λ _ → sym (C.Hom.assoc _ _ _) ∙ C.pentagon-α→
