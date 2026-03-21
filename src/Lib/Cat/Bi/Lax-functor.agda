open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Functor.Base
open import Cat.Functor.Naturality
open import Cat.Instances.Product

import Cat.Functor.Reasoning as Fr
import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Lib.Cat.Bi.Lax-functor where

private variable
  o1 o2 o3 h1 h2 h3 l1 l2 l3 : Level

open _=>_

module Lf-reasoning
  {B : Prebicategory o1 h1 l1} {C : Prebicategory o2 h2 l2}
  (F : Lax-functor B C) where

  private
    module B = Prebicategory B
    module C = Prebicategory C

  module P₁ {A} {B} = Fr (Lax-functor.P₁ F {A} {B})

  open Lax-functor F hiding (module P₁) public

  ▶-comp
    : ∀ {X Y Z} {f : Y B.↦ Z}
    → postaction C (₁ f) F∘ P₁ {X} {Y} => P₁ F∘ postaction B f
  ▶-comp .η x              = γ→ (_ , x)
  ▶-comp .is-natural _ _ α =
    ap (λ f → γ→ _ C.∘ (f C.◆ ₂ α)) (sym P₁.F-id) ∙ γ→nat _ _

  ◀-comp
    : ∀ {X Y Z} {f : X B.↦ Y}
    → preaction C (₁ f) F∘ P₁ {Y} {Z} => P₁ F∘ preaction B f
  ◀-comp .η x              = γ→ (x , _)
  ◀-comp .is-natural _ _ α =
    ap (λ f → γ→ _ C.∘ (₂ α C.◆ f)) (sym P₁.F-id) ∙ γ→nat _ _

module Pf-reasoning
  {B : Prebicategory o1 h1 l1} {C : Prebicategory o2 h2 l2}
  (F : Pseudofunctor B C) where

  private
    module B = Prebicategory B
    module C = Br C

  module P₁ {A} {B} = Fr (Pseudofunctor.P₁ F {A} {B})

  open Pseudofunctor F hiding (module P₁) public

  open Cr._≅_
  open Cr.Inverses

  υ≅ : ∀ {A} → C.id C.Hom.≅ ₁ (B.id {A})
  υ≅ .to       = υ→
  υ≅ .from     = υ←
  υ≅ .inverses = Cr.is-invertible.inverses unitor-inv

  compositor-ni :
    ∀ {A B C} → C.compose F∘ (P₁ {B} {C} F× P₁ {A} {B}) ≅ⁿ P₁ F∘ B.compose
  compositor-ni = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta       = γ→
    ni .make-natural-iso.inv       = γ←
    ni .make-natural-iso.eta∘inv _ =
      Cr.is-invertible.inverses (compositor-inv _) .invl
    ni .make-natural-iso.inv∘eta _ =
      Cr.is-invertible.inverses (compositor-inv _) .invr
    ni .make-natural-iso.natural _ _ _ = sym $ γ→nat _ _

  γ≅ : ∀ {A B C} {f : B B.↦ C} {g : A B.↦ B} → ₁ f C.⊗ ₁ g C.Hom.≅ ₁ (f B.⊗ g)
  γ≅ = isoⁿ→iso compositor-ni _

  ▶-comp
    : ∀ {X Y Z} {f : Y B.↦ Z}
    → postaction C (₁ f) F∘ P₁ {X} {Y} ≅ⁿ P₁ F∘ postaction B f
  ▶-comp = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta x     = γ→ (_ , x)
    ni .make-natural-iso.inv x     = γ← (_ , x)
    ni .make-natural-iso.eta∘inv _ =
      Cr.is-invertible.inverses (compositor-inv _) .invl
    ni .make-natural-iso.inv∘eta _ =
      Cr.is-invertible.inverses (compositor-inv _) .invr
    ni .make-natural-iso.natural _ _ α =
      sym $ ap (λ f → γ→ _ C.∘ (f C.◆ ₂ α)) (sym P₁.F-id) ∙ γ→nat _ _

  ◀-comp
    : ∀ {X Y Z} {f : X B.↦ Y}
    → preaction C (₁ f) F∘ P₁ {Y} {Z} ≅ⁿ P₁ F∘ preaction B f
  ◀-comp = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta x     = γ→ (x , _)
    ni .make-natural-iso.inv x     = γ← (x , _)
    ni .make-natural-iso.eta∘inv _ =
      Cr.is-invertible.inverses (compositor-inv _) .invl
    ni .make-natural-iso.inv∘eta _ =
      Cr.is-invertible.inverses (compositor-inv _) .invr
    ni .make-natural-iso.natural _ _ α =
      sym $ ap (λ f → γ→ _ C.∘ (₂ α C.◆ f)) (sym P₁.F-id) ∙ γ→nat _ _


open Pseudofunctor
open Lax-functor

module _ {B : Prebicategory o1 h1 l1} where
  open Br B

  IdL : Lax-functor B B
  IdL .P₀ z                         = z
  IdL .P₁                           = Id
  IdL .compositor .η x              = Hom.id
  IdL .compositor .is-natural _ _ _ = Hom.id-comm-sym
  IdL .unitor                       = Hom.id
  IdL .hexagon f g h =
    Hom.elimr (Hom.idl _ ∙ ⊗.F-id) ∙ Hom.insertl (Hom.idl _ ∙ ⊗.F-id)
  IdL .right-unit f = Hom.elimr (Hom.idl _ ∙ ⊗.F-id)
  IdL .left-unit f  = Hom.elimr (Hom.idl _ ∙ ⊗.F-id)

  IdP : Pseudofunctor B B
  IdP .lax              = IdL
  IdP .unitor-inv       = Hom.id-invertible
  IdP .compositor-inv _ = Hom.id-invertible

module _
  {B : Prebicategory o1 h1 l1} {C : Prebicategory o2 h2 l2}
  {D : Prebicategory o3 h3 l3}
  where
  private
    module B  = Prebicategory B
    module C  = Prebicategory C
    module D  = Br D
    module DH = D.Hom
    module Pr = Pf-reasoning

  _L∘_ : Lax-functor C D → Lax-functor B C → Lax-functor B D
  _L∘_ F G = lf module L∘ where
    private
      module F = Lf-reasoning F
      module G = Lax-functor G
    lf : Lax-functor _ _
    lf .P₀                    = F.P₀ ⊙ G.P₀
    lf .P₁                    = F.P₁ F∘ G.P₁
    lf .compositor .η (x , y) = F.₂ (G.γ→ (x , y)) D.∘ F.γ→ (G.₁ x , G.₁ y)
    lf .compositor .is-natural (x , y) (x' , y') (f , g) =
      (F.₂ (G.γ→ _) D.∘ F.γ→ _) D.∘ (F.₂ (G.₂ f) D.◆ F.₂ (G.₂ g)) ≡⟨ DH.extendr (F.γ→nat (G.₂ f) (G.₂ g)) ⟩
      (F.₂ (G.γ→ _) D.∘ F.₂ (G.₂ f C.◆ G.₂ g)) D.∘ F.γ→ _         ≡⟨ DH.pushl (F.P₁.weave (G.γ→nat f g)) ⟩
      F.₂ (G.₂ (f B.◆ g)) D.∘ F.₂ (G.γ→ _) D.∘ F.γ→ _             ∎
    lf .unitor        = F.₂ G.υ→ D.∘ F.υ→
    lf .hexagon f g h =
          F.₂ (G.₂ (B.α→ _)) D.∘ (F.₂ (G.γ→ _) D.∘ F.γ→ _)
      D.∘ (F.₂ (G.γ→ _) D.∘ F.γ→ _) D.◀ F.₁ (G.₁ h)
        ≡˘⟨ DH.refl⟩∘⟨ DH.pushr (DH.extendl (sym $ F.◀-comp .is-natural _ _ _) ∙ ap (F.γ→ _ D.∘_) (sym D.◀-distribl)) ⟩
          F.₂ (G.₂ (B.α→ _)) D.∘ F.₂ (G.γ→ _) D.∘ F.₂ (G.γ→ _ C.◀ G.₁ h) D.∘ F.γ→ _
      D.∘ F.γ→ _ D.◀ F.₁ (G.₁ h)
        ≡⟨ F.P₁.extendl3 (G.hexagon f g h) ⟩
          F.₂ (G.γ→ _) D.∘ F.₂ (G.₁ f C.▶ G.γ→ _) D.∘ F.₂ (C.α→ _)
      D.∘ F.γ→ _ D.∘ F.γ→ _ D.◀ F.₁ (G.₁ h)
        ≡⟨ DH.refl⟩∘⟨ DH.refl⟩∘⟨ F.hexagon (G.₁ f) (G.₁ g) (G.₁ h) ⟩
          F.₂ (G.γ→ _) D.∘ F.₂ (G.₁ f C.▶ G.γ→ _) D.∘ F.γ→ _
      D.∘ F.₁ (G.₁ f) D.▶ F.γ→ _ D.∘ D.α→ _
        ≡⟨ DH.refl⟩∘⟨ DH.extendl (sym $ F.▶-comp .is-natural _ _ _) ⟩
          F.₂ (G.γ→ _) D.∘ F.γ→ _ D.∘ F.₁ (G.₁ f) D.▶ F.₂ (G.γ→ _)
      D.∘ F.₁ (G.₁ f) D.▶ F.γ→ _ D.∘ D.α→ _
        ≡⟨ DH.pushr (ap (F.γ→ _ D.∘_) (D.▶.pulll refl)) ⟩
          (F.₂ (G.γ→ (f , g B.⊗ h)) D.∘ F.γ→ (G.₁ f , G.₁ (g B.⊗ h)))
      D.∘ F.₁ (G.₁ f) D.▶ (F.₂ (G.γ→ (g , h)) D.∘ F.γ→ (G.₁ g , G.₁ h)) D.∘ D.α→ _
        ∎
    lf .right-unit f =
          F.₂ (G.₂ (B.ρ← f)) D.∘ (F.₂ (G.γ→ (f , B.id)) D.∘ F.γ→ (G.₁ f , G.₁ B.id))
      D.∘ F.₁ (G.₁ f) D.▶ (F.₂ G.υ→ D.∘ F.υ→)
        ≡˘⟨ DH.refl⟩∘⟨ DH.pushr (DH.extendl (sym $ F.▶-comp .is-natural _ _ _) ∙ ap (F.γ→ _ D.∘_) (sym D.▶-distribr)) ⟩
          F.₂ (G.₂ (B.ρ← f)) D.∘ F.₂ (G.γ→ (f , B.id)) D.∘ F.₂ (G.₁ f C.▶ G.υ→)
      D.∘ F.γ→ (G.₁ f , C.id) D.∘ F.₁ (G.₁ f) D.▶ F.υ→
        ≡⟨ F.P₁.pulll3 (G.right-unit f) ⟩
      F.₂ (C.ρ← (G.₁ f)) D.∘ F.γ→ (G.₁ f , C.id) D.∘ F.₁ (G.₁ f) D.▶ F.υ→
        ≡⟨ F.right-unit (G.₁ f) ⟩
      D.ρ← (F.₁ (G.₁ f))
        ∎
    lf .left-unit f =
          F.₂ (G.₂ (B.λ← f)) D.∘ (F.₂ (G.γ→ (B.id , f)) D.∘ F.γ→ (G.₁ B.id , G.₁ f))
      D.∘ (F.₂ G.υ→ D.∘ F.υ→) D.◀ F.₁ (G.₁ f)
        ≡˘⟨ DH.refl⟩∘⟨ DH.pushr (DH.extendl (sym $ F.◀-comp .is-natural _ _ _) ∙ ap (F.γ→ _ D.∘_) (sym D.◀-distribl)) ⟩
          F.₂ (G.₂ (B.λ← f)) D.∘ F.₂ (G.γ→ (B.id , f)) D.∘ F.₂ (G.υ→ C.◀ G.₁ f)
      D.∘ F.γ→ (C.id , G.₁ f) D.∘ F.υ→ D.◀ F.₁ (G.₁ f)
        ≡⟨ F.P₁.pulll3 (G.left-unit f) ⟩
      F.₂ (C.λ← (G.₁ f)) D.∘ F.γ→ (C.id , G.₁ f) D.∘ F.υ→ D.◀ F.₁ (G.₁ f)
        ≡⟨ F.left-unit (G.₁ f) ⟩
      D.λ← (F.₁ (G.₁ f))
        ∎

  {-# DISPLAY L∘.lf F G = F L∘ G #-}

  _P∘_ : Pseudofunctor C D → Pseudofunctor B C → Pseudofunctor B D
  (F P∘ G) .lax        = F .lax L∘ G .lax
  (F P∘ G) .unitor-inv = DH.invertible-∘
    (Pr.P₁.F-map-invertible F (Pr.unitor-inv G)) (Pr.unitor-inv F)
  (F P∘ G) .compositor-inv _ = DH.invertible-∘
    (Pr.P₁.F-map-invertible F (Pr.compositor-inv G _)) (Pr.compositor-inv F _)
