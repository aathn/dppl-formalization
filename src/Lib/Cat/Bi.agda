module Lib.Cat.Bi where

open import Lib.Cat.Product

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Functor.Base
open import Cat.Functor.Compose hiding (_◆_)
open import Cat.Functor.Constant
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Naturality
open import Cat.Instances.Discrete
open import Cat.Instances.Product
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr

open Functor
open _=>_

module Reasoning {o ℓ ℓ'} (C : Prebicategory o ℓ ℓ') where
  open Prebicategory C public hiding (module Hom)

  module Hom {a b} = Cr (Hom a b)
  module ⊗ {a b c} = Fr (compose {a} {b} {c})
  module ▶ {a b c} {f} = Fr (postaction C {a} {b} {c} f)
  module ◀ {a b c} {f} = Fr (preaction C {a} {b} {c} f)

  open Hom hiding (Ob ; id ; _∘_ ; to ; from)
  open Cr._≅_

  private variable
    X Y Z : Ob
    f g h k : X ↦ Y
    α : g ⇒ h
    β : f ⇒ g

  ρ≅ : f ≅ f ⊗ id
  ρ≅ = isoⁿ→iso unitor-r _

  λ≅ : f ≅ id ⊗ f
  λ≅ = isoⁿ→iso unitor-l _

  α≅ : (f ⊗ g) ⊗ h ≅ f ⊗ (g ⊗ h)
  α≅ = isoⁿ→iso associator _

  ▶-distribr : h ▶ (α ∘ β) ≡ h ▶ α ∘ h ▶ β
  ▶-distribr = ▶.F-∘ _ _

  ◀-distribl : (α ∘ β) ◀ h ≡ α ◀ h ∘ β ◀ h
  ◀-distribl = ◀.F-∘ _ _

  ▶-assoc : ∀ {c} → postaction C {c = c} (f ⊗ g) ≅ⁿ postaction C f F∘ postaction C g
  ▶-assoc {f = f} {g = g} = to-natural-iso record
    { eta = λ x → α→ f g x
    ; inv = λ x → α← f g x
    ; eta∘inv = λ _ → α≅ .invl
    ; inv∘eta = λ _ → α≅ .invr
    ; natural = λ _ _ _ → sym (α→nat _ _ _) ∙ ap ((α→ _ _ _ ∘_) ⊙ (_◆ _)) ⊗.F-id
    }

  ◀-assoc : ∀ {c} → preaction C {c = c} (f ⊗ g) ≅ⁿ preaction C g F∘ preaction C f
  ◀-assoc {f = f} {g = g} = to-natural-iso record
    { eta = λ x → α← x f g
    ; inv = λ x → α→ x f g
    ; eta∘inv = λ _ → α≅ .invr
    ; inv∘eta = λ _ → α≅ .invl
    ; natural = λ _ _ _ → sym (α←nat _ _ _) ∙ ap ((α← _ _ _ ∘_) ⊙ (_ ◆_)) ⊗.F-id
    }

  ◀-▶-comm : preaction C f F∘ postaction C g ≅ⁿ postaction C g F∘ preaction C f
  ◀-▶-comm {f = f} {g = g} = to-natural-iso record
    { eta = λ x → α→ g x f
    ; inv = λ x → α← g x f
    ; eta∘inv = λ _ → α≅ .invl
    ; inv∘eta = λ _ → α≅ .invr
    ; natural = λ _ _ _ → sym (α→nat _ _ _)
    }

  -- Several proofs below taken from Cat.Monoidal.Base.

  triangle-α→ : (f ▶ λ← g) ∘ α→ _ _ _ ≡ ρ← f ◀ g
  triangle-α→ = rswizzle (sym $ triangle _ _) (α≅ .invr)

  pentagon-α→
    : (f ▶ α→ g h k) ∘ α→ f (g ⊗ h) k ∘ (α→ f g h ◀ k)
    ≡ α→ f g (h ⊗ k) ∘ α→ (f ⊗ g) h k
  pentagon-α→ = inverse-unique refl refl
    (▶.F-map-iso (α≅ Iso⁻¹) ∙Iso α≅ Iso⁻¹ ∙Iso ◀.F-map-iso (α≅ Iso⁻¹))
    (α≅ Iso⁻¹ ∙Iso α≅ Iso⁻¹)
    (sym (assoc _ _ _) ∙ pentagon _ _ _ _)

-- Below is the corresponding prism diagram for the triangle-ρ← identity.
-- \[\begin{tikzcd}
-- 	& {A\otimes (B\otimes (1 \otimes 1))} \\
-- 	{A\otimes ((B\otimes 1)\otimes 1)} & {(A \otimes B)\otimes (1 \otimes 1)} & {A\otimes (B \otimes 1)} \\
-- 	& {((A\otimes B)\otimes 1)\otimes 1} \\
-- 	{(A\otimes (B \otimes 1))\otimes 1} && {(A\otimes B)\otimes 1}
-- 	\arrow["{\alpha^{-1}}", dashed, from=1-2, to=2-2]
-- 	\arrow["{{A\otimes (B\otimes \lambda)}}", from=1-2, to=2-3]
-- 	\arrow["{{A\otimes \alpha}}", from=2-1, to=1-2]
-- 	\arrow["{{A\otimes (\rho \otimes 1)}}"'{pos=0.2}, curve={height=6pt}, from=2-1, to=2-3]
-- 	\arrow["{\alpha^{-1}}", from=2-1, to=4-1]
-- 	\arrow["{\alpha^{-1}}", dashed, from=2-2, to=3-2]
-- 	\arrow["{\alpha^{-1}}"', from=2-3, to=4-3]
-- 	\arrow["{{\rho \otimes 1}}"', dashed, from=3-2, to=4-3]
-- 	\arrow["{{\alpha^{-1} \otimes 1}}"', dashed, from=4-1, to=3-2]
-- 	\arrow["{{(A \otimes \rho)\otimes 1}}"', from=4-1, to=4-3]
-- \end{tikzcd}\]

  triangle-ρ← : ρ← (f ⊗ g) ∘ α← f g id ≡ f ▶ ρ← g
  triangle-ρ← {f = f} {g = g} = push-eqⁿ (unitor-r ni⁻¹) $
    ◀.F-∘ _ _ ∙ ap to (Iso-prism base sq1 sq2 sq3)
    where
      base : ▶.F-map-iso α≅ ∙Iso ▶.F-map-iso (▶.F-map-iso (λ≅ Iso⁻¹))
           ≡ ▶.F-map-iso (◀.F-map-iso (ρ≅ Iso⁻¹))
      base = ≅-path (▶.collapse triangle-α→)

      sq1 : ▶.F-map-iso α≅ ∙Iso α≅ Iso⁻¹ ∙Iso α≅ Iso⁻¹ ≡ α≅ Iso⁻¹ ∙Iso ◀.F-map-iso (α≅ Iso⁻¹)
      sq1 = ≅-path (rswizzle (sym (pentagon _ _ _ _) ∙ assoc _ _ _) 
        (▶.annihilate (α≅ .invr)))

      sq2 : ▶.F-map-iso (▶.F-map-iso (λ≅ Iso⁻¹)) ∙Iso α≅ Iso⁻¹
          ≡ (α≅ Iso⁻¹ ∙Iso α≅ Iso⁻¹) ∙Iso ◀.F-map-iso (ρ≅ Iso⁻¹)
      sq2 = ≅-path $ ▶-assoc .from .is-natural _ _ _ ∙ sym (pulll (triangle _ _))

      sq3 : ▶.F-map-iso (◀.F-map-iso (ρ≅ Iso⁻¹)) ∙Iso α≅ Iso⁻¹
          ≡ α≅ Iso⁻¹ ∙Iso ◀.F-map-iso (▶.F-map-iso (ρ≅ Iso⁻¹))
      sq3 = ≅-path (α←nat _ _ _)

  triangle-ρ→ : ρ→ (f ⊗ g) ≡ α← f g id ∘ f ▶ ρ→ g
  triangle-ρ→ {f = f} {g = g} =
    ρ→ (f ⊗ g)                                     ≡⟨ intror (sym ▶-distribr ∙ ▶.elim (ρ≅ .invr)) ⟩
    ρ→ (f ⊗ g) ∘ f ▶ ρ← g ∘ f ▶ ρ→ g               ≡⟨ refl⟩∘⟨ pushl (sym triangle-ρ←) ⟩
    ρ→ (f ⊗ g) ∘ ρ← (f ⊗ g) ∘ α← f g id ∘ f ▶ ρ→ g ≡⟨ cancell (ρ≅ .invl) ⟩
    α← f g id ∘ f ▶ ρ→ g                           ∎

  triangle-λ← : λ← (f ⊗ g) ∘ α→ id f g ≡ λ← f ◀ g
  triangle-λ← {f = f} {g = g} = push-eqⁿ (unitor-l ni⁻¹) $
    ▶.F-∘ _ _ ∙ ap to (Iso-prism base sq1 sq2 sq3)
    where
      base : ◀.F-map-iso (α≅ Iso⁻¹) ∙Iso ◀.F-map-iso (◀.F-map-iso (ρ≅ Iso⁻¹))
           ≡ ◀.F-map-iso (▶.F-map-iso (λ≅ Iso⁻¹))
      base = ≅-path (◀.collapse (triangle _ _))

      sq1 : ◀.F-map-iso (α≅ Iso⁻¹) ∙Iso α≅ ∙Iso α≅ ≡ α≅ ∙Iso ▶.F-map-iso α≅
      sq1 = ≅-path (rswizzle (sym pentagon-α→ ∙ assoc _ _ _)
        (◀.annihilate (α≅ .invl)))

      sq2 : ◀.F-map-iso (◀.F-map-iso (ρ≅ Iso⁻¹)) ∙Iso α≅
          ≡ (α≅ ∙Iso α≅) ∙Iso ▶.F-map-iso (λ≅ Iso⁻¹)
      sq2 = ≅-path $ ◀-assoc .from .is-natural _ _ _ ∙ sym (pulll triangle-α→)

      sq3 : ◀.F-map-iso (▶.F-map-iso (λ≅ Iso⁻¹)) ∙Iso α≅
          ≡ α≅ ∙Iso ▶.F-map-iso (◀.F-map-iso (λ≅ Iso⁻¹))
      sq3 = ≅-path (α→nat _ _ _)

  triangle-λ→ : λ→ (f ⊗ g) ≡ α→ id f g ∘ λ→ f ◀ g
  triangle-λ→ {f = f} {g = g} =
    λ→ (f ⊗ g)                                     ≡⟨ intror (sym ◀-distribl ∙ ◀.elim (λ≅ .invr)) ⟩
    λ→ (f ⊗ g) ∘ λ← f ◀ g ∘ λ→ f ◀ g               ≡⟨ refl⟩∘⟨ pushl (sym triangle-λ←) ⟩
    λ→ (f ⊗ g) ∘ λ← (f ⊗ g) ∘ α→ id f g ∘ λ→ f ◀ g ≡⟨ cancell (λ≅ .invl) ⟩
    α→ id f g ∘ λ→ f ◀ g                           ∎

  λ←≡ρ← : ∀ {A} → λ← (id {A}) ≡ ρ← id
  λ←≡ρ← = push-eqⁿ (unitor-r ni⁻¹) $
    (λ← id ◀ id)           ≡˘⟨ triangle-λ← ⟩
    λ← _ ∘ α→ _ _ _        ≡⟨ (insertl (λ≅ .invl) ∙∙ refl⟩∘⟨ sym (λ←nat _) ∙∙ cancell (λ≅ .invl)) ⟩∘⟨refl ⟩
    (id ▶ λ← _) ∘ α→ _ _ _ ≡⟨ triangle-α→ ⟩
    (ρ← id ◀ id)           ∎

  λ→≡ρ→ : ∀ {A} → λ→ (id {A}) ≡ ρ→ id
  λ→≡ρ→ =
    λ→ id                 ≡⟨ intror (ρ≅ .invr) ⟩
    λ→ id ∘ ρ← id ∘ ρ→ id ≡˘⟨ refl⟩∘⟨ λ←≡ρ← ⟩∘⟨refl ⟩
    λ→ id ∘ λ← id ∘ ρ→ id ≡⟨ cancell (λ≅ .invl) ⟩
    ρ→ id                 ∎


module _ {o h ℓ ℓx ℓp} (BC : Prebicategory o h ℓ) (O : Prebicategory.Ob BC → Type ℓx) where
  open Prebicategory
  private
    module BC = Reasoning BC

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
        → H A B F → H B C G → H A C (G BC.⊗ F))
    → Prebicategory (o ⊔ ℓx) (h ⊔ ℓp) ℓ
  Birestrict H H-id H-∘ = pb where
    open Cr._≅_
    open Cr.Inverses

    B[_,_] : Ob' → Ob' → Precategory _ _
    B[ A , B ] = Restrict {C = B'[ A , B ]} (H A B)

    B-id : {C : Ob'} → ⌞ B[ C , C ] ⌟
    B-id = BC.id , H-id

    B-compose : {A B C : Ob'} → Functor (B[ B , C ] ×ᶜ B[ A , B ]) B[ A , C ]
    B-compose = record
      { F₀   = λ ((F , F-mor) , (G , G-mor)) → F BC.⊗ G , H-∘ G F G-mor F-mor
      ; F₁   = BC.⊗.₁
      ; F-id = BC.⊗.F-id
      ; F-∘  = BC.⊗.F-∘
      }

    B-assoc : Associator-for B[_,_] B-compose
    B-assoc = to-natural-iso record
      { eta = λ _ → BC.α≅ .to
      ; inv = λ _ → BC.α≅ .from
      ; eta∘inv = λ _ → BC.α≅ .invl
      ; inv∘eta = λ _ → BC.α≅ .invr
      ; natural = λ _ _ _ → sym $ BC.α→nat _ _ _
      }

    pb : Prebicategory _ _ _
    pb .Ob = Ob'
    pb .Hom = B[_,_]
    pb .id = B-id
    pb .compose = B-compose
    pb .unitor-r = to-natural-iso record
      { eta = λ _ → BC.ρ≅ .to
      ; inv = λ _ → BC.ρ≅ .from
      ; eta∘inv = λ (f , _) → BC.ρ≅ .invl
      ; inv∘eta = λ (f , _) → BC.ρ≅ .invr
      ; natural = λ _ _ _ → sym $ BC.ρ→nat _
      }
    pb .unitor-l = to-natural-iso record
      { eta = λ _ → BC.λ≅ .to
      ; inv = λ _ → BC.λ≅ .from
      ; eta∘inv = λ (f , _) → BC.λ≅ .invl
      ; inv∘eta = λ (f , _) → BC.λ≅ .invr
      ; natural = λ _ _ _ → sym $ BC.λ→nat _
      }
    pb .associator = B-assoc
    pb .triangle (f , _) (g , _) = BC.triangle f g
    pb .pentagon (f , _) (g , _) (h , _) (i , _) = BC.pentagon f g h i


cat→bicat : ∀ {o ℓ} → Precategory o ℓ → Prebicategory o ℓ ℓ
cat→bicat C = pb where
  module C = Precategory C
  open Prebicategory

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


module _ {o h ℓ} {C : Prebicategory o h ℓ} where
  open Reasoning C
  private
    module H = Hom
    module Cat = Prebicategory (Cat h ℓ)

  module _ (X : Ob) where
    open Lax-functor
    open Cr._≅_
    open Cr.Inverses

    Hom-from-bi₁ : ∀ {A B} → Functor (Hom A B) Cat[ Hom X A , Hom X B ]
    Hom-from-bi₁ .F₀ f = compose F∘ Cat⟨ Const f , Id ⟩
    Hom-from-bi₁ .F₁ α = compose ▸ (constⁿ α nt, idnt)
    Hom-from-bi₁ .F-id    = ext λ _ → ⊗.F-id
    Hom-from-bi₁ .F-∘ f g = ext λ _ → ◀-distribl

    Hom-from-bi : Lax-functor C (Cat h ℓ)
    Hom-from-bi = lf where

      Hom-compositor : ∀ {A B C} → Cat.compose F∘ (Hom-from-bi₁ {B} {C} F× Hom-from-bi₁ {A} {B}) => Hom-from-bi₁ F∘ compose
      Hom-compositor .η (f , g) .η = α← f g
      Hom-compositor .η (f , g) .is-natural x y h =
        α← f g y ∘ (H.id ◆ (H.id ◆ h)) ≡⟨ α←nat H.id H.id h ⟩
        ((H.id ◆ H.id) ◆ h) ∘ α← f g x ≡⟨ ap (_◆ _) ⊗.F-id H.⟩∘⟨refl ⟩
        (H.id ◆ h) ∘ α← f g x          ∎
      Hom-compositor .is-natural (f , g) (f' , g') (α , β) = ext λ h →
        α← f' g' h ∘ (H.id ◆ (β ◆ H.id)) ∘ (α ◆ H.id)   ≡˘⟨ H.refl⟩∘⟨ ⊗.F-∘ _ _ ⟩
        α← f' g' h ∘ ((H.id ∘ α) ◆ ((β ◆ H.id) ∘ H.id)) ≡⟨ H.refl⟩∘⟨ ⊗.⟨ ap₂ _,_ (H.idl _) (H.idr _) ⟩ ⟩
        α← f' g' h ∘ (α ◆ (β ◆ H.id))                   ≡⟨ α←nat α β H.id ⟩
        ((α ◆ β) ◆ H.id) ∘ α← f g h                     ∎

      Hom-unitor : ∀ {A} → Cat.id => Hom-from-bi₁ {A} {A} .F₀ id
      Hom-unitor .η f = λ→ f ∘ H.id
      Hom-unitor .is-natural _ _ α =
        ap (_∘ _) (H.idr _) ∙ λ→nat α ∙ ap ((H.id ◆ α) ∘_) (sym $ H.idr _)

      lf : Lax-functor _ _
      lf .P₀ = Hom X
      lf .P₁ = Hom-from-bi₁
      lf .compositor = Hom-compositor
      lf .unitor = Hom-unitor
      lf .hexagon f g h = ext λ u →
        α→ f g h ◀ u ∘ α← (f ⊗ g) h u ∘ _ ∘ α← f g (h ⊗ u)          ≡⟨ H.refl⟩∘⟨ H.refl⟩∘⟨ ⊗.eliml refl ⟩
        α→ f g h ◀ u ∘ α← (f ⊗ g) h u ∘ α← f g (h ⊗ u)              ≡˘⟨ H.refl⟩∘⟨ pentagon f g h u ⟩
        α→ f g h ◀ u ∘ α← f g h ◀ u ∘ α← f (g ⊗ h) u ∘ f ▶ α← g h u ≡⟨ H.pulll $ sym ◀-distribl ⟩
        (α→ f g h ∘ α← f g h) ◀ u ∘ α← f (g ⊗ h) u ∘ f ▶ α← g h u   ≡⟨ ap (_◀ u) (α≅ .invl) H.⟩∘⟨refl ⟩
        (H.id ◀ u) ∘ α← f (g ⊗ h) u ∘ f ▶ α← g h u                  ≡⟨ ⊗.eliml refl ∙ ap (α← _ _ _ ∘_) (sym $ H.idr _ ∙ H.idr _) ⟩
        α← f (g ⊗ h) u ∘ ((f ▶ α← g h u) H.∘ H.id) ∘ H.id           ∎
      lf .right-unit f = ext λ h →
        ρ← f ◀ h ∘ α← f id h ∘ f ▶ (λ→ h ∘ _) ∘ _ ≡⟨ H.refl⟩∘⟨ H.refl⟩∘⟨ H.idr _ ∙ ap (H.id ◆_) (H.idr _) ⟩
        ρ← f ◀ h ∘ α← f id h ∘ f ▶ λ→ h           ≡⟨ H.pulll (triangle f h) ∙ sym ▶-distribr ⟩
        f ▶ (λ← h ∘ λ→ h)                         ≡⟨ ap (f ▶_) (λ≅ .invr) ∙ ⊗.F-id ⟩
        H.id                                      ∎
      lf .left-unit  f = ext λ h →
        λ← f ◀ h ∘ α← id f h ∘ _ ∘ λ→ (f ⊗ h) ∘ _ ≡⟨ H.refl⟩∘⟨ H.refl⟩∘⟨ ⊗.eliml refl ∙ H.idr _ ⟩
        λ← f ◀ h ∘ α← id f h ∘ λ→ (f ⊗ h)         ≡⟨ H.pushl $ sym triangle-λ← ⟩
        λ← _ ∘ α→ id f h ∘ α← id f h ∘ λ→ _       ≡⟨ H.refl⟩∘⟨ H.cancell (α≅ .invl) ⟩
        λ← (f ⊗ h) ∘ λ→ (f ⊗ h)                   ≡⟨ λ≅ .invr ⟩
        H.id                                      ∎
