open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Functor.Base

import Cat.Functor.Reasoning as Fr
import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Lib.Cat.Bi.Lax-functor where

private variable
  o o' h h' ℓ ℓ' : Level
  B C D : Prebicategory o h ℓ

open _=>_

module Reasoning
  {B : Prebicategory o h ℓ} {C : Prebicategory o' h' ℓ'}
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

open Lax-functor
open Pseudofunctor

IdL : Lax-functor B B
IdL {B = B} = lf where
  open Br B
  lf : Lax-functor _ _
  lf .P₀ z                         = z
  lf .P₁                           = Id
  lf .compositor .η x              = Hom.id
  lf .compositor .is-natural _ _ _ = Hom.id-comm-sym
  lf .unitor                       = Hom.id
  lf .hexagon f g h =
    Hom.elimr (Hom.idl _ ∙ ⊗.F-id) ∙ Hom.insertl (Hom.idl _ ∙ ⊗.F-id)
  lf .right-unit f = Hom.elimr (Hom.idl _ ∙ ⊗.F-id)
  lf .left-unit f  = Hom.elimr (Hom.idl _ ∙ ⊗.F-id)

_L∘_ : Lax-functor C D → Lax-functor B C → Lax-functor B D
_L∘_ {C = C} {D = D} {B = B} F G = lf where
  module B = Prebicategory B
  module C = Prebicategory C
  module D = Br D
  module DH = D.Hom
  module F = Reasoning F
  module G = Lax-functor G
  lf : Lax-functor _ _
  lf .P₀ = F.P₀ ⊙ G.P₀
  lf .P₁ = F.P₁ F∘ G.P₁
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

IdP : Pseudofunctor B B
IdP {B = B} = pf where
  open Prebicategory B
  pf : Pseudofunctor _ _
  pf .lax              = IdL
  pf .unitor-inv       = Cr.id-invertible (Hom _ _)
  pf .compositor-inv _ = Cr.id-invertible (Hom _ _)

_P∘_ : Pseudofunctor C D → Pseudofunctor B C → Pseudofunctor B D
_P∘_ {C = C} {D = D} {B = B} F G = pf where
  open Prebicategory D
  module F = Pseudofunctor F
  module G = Pseudofunctor G
  pf : Pseudofunctor _ _
  pf .lax        = F.lax L∘ G.lax
  pf .unitor-inv = Cr.invertible-∘ (Hom _ _)
    (F-iso.F-map-invertible F.P₁ G.unitor-inv) F.unitor-inv
  pf .compositor-inv _ = Cr.invertible-∘ (Hom _ _)
    (F-iso.F-map-invertible F.P₁ (G.compositor-inv _)) (F.compositor-inv _)
