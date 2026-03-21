open import Cat.Bi.Instances.Discrete
open import Cat.Instances.Discrete
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Groupoid
open import Cat.Bi.Base
open import Cat.Prelude

open import Lib.Cat.Bi.Construction
open import Lib.Cat.Bi.Equivalence
open import Lib.Cat.Bi.Lax-functor
open import Lib.Cat.Bi.Duality hiding (_^op)

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr

module Lib.Cat.Bi.Colimit where

private variable
  o h ℓ o' h' ℓ' : Level

module _
  {I : Prebicategory o h ℓ}
  {C : Prebicategory o' (o ⊔ h ⊔ ℓ ⊔ h' ⊔ ℓ') (o ⊔ h ⊔ ℓ ⊔ ℓ')}
  where
  open Prebicategory C
  open Pseudofunctor

  is-lax-colim : Pseudofunctor I C → Ob → Type _
  is-lax-colim F L = Equivalenceᵖ (lhs .lax) (rhs .lax) where
    lhs = Hom-from-bi (Pseudoₒ I C) (co F) P∘ Const-pseudoₒ
    rhs = Hom-from-bi C L

module _
  {I : Precategory o h}
  (F : Pseudofunctor (Locally-discrete (I ^op)) (Cat o' h'))
  where
  open Displayed
  open Functor
  open _=>_
  private
    module I = Precategory I
    module F = Pf-reasoning F
    open module F₀ {x} = Cr (F.₀ x)

    module LD = Prebicategory (Locally-discrete (I ^op))
    module pg {x} {y} = is-pregroupoid {C = LD.Hom y x} Disc-is-groupoid

    abstract
      F₁-path
        : ∀ {A} {B} {f g : I.Hom A B} {Fx} (p : f ≡ g)
        → path→iso (ap (λ x → x .F₀ Fx) (ap· F.P₁ p)) .to ≡ F.₂ p .η Fx
      F₁-path {Fx = Fx} p = sym Regularity.reduce!
        ∙ ap Cr._≅_.to (F-iso.ap-F₀-iso F.P₁ Disc-is-category (pg.hom→iso p)) ηₚ Fx

  Fibration : Displayed I _ _
  Fibration .Ob[_] x                  = F₀.Ob {x}
  Fibration .Hom[_] {x} f Fx Fy       = F₀.Hom Fx (F.₁ f .F₀ Fy)
  Fibration .Hom[_]-set _ _ _         = hlevel 2
  Fibration .id'                      = F.υ→ .η _
  Fibration ._∘'_ {g = g} Ff Fg       = F.γ→ _ .η _ ∘ F.₁ g .F₁ Ff ∘ Fg
  Fibration .idr' {x} {y = Fy} {f} Ff = Hom-pathp-reflr (F.₀ x) $
      path→iso (ap (λ x → x .F₀ Fy) (ap· F.P₁ (I.idr f))) ._≅_.to
    ∘ F.γ→ _ .η Fy ∘ F.₁ I.id .F₁ Ff ∘ F.υ→ .η _                          ≡⟨ F₁-path (I.idr f) ⟩∘⟨refl ⟩
    F.₂ (I.idr f) .η Fy ∘ F.γ→ _ .η Fy ∘ F.₁ I.id .F₁ Ff ∘ F.υ→ .η _      ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ eliml (F.₁ I.id .F-id) ∙ F.υ→ .is-natural _ _ _ ⟩
    F.₂ (I.idr f) .η Fy ∘ F.γ→ _ .η Fy ∘ F.₁ I.id .F₁ id ∘ F.υ→ .η _ ∘ Ff ≡⟨ pulll4 (F.left-unit f ηₚ Fy) ∙ idl _ ⟩
    Ff                                                                    ∎
  Fibration .idl' {x} {y = Fy} {f} Ff = Hom-pathp-reflr (F.₀ x) $
      path→iso (ap (λ x → x .F₀ Fy) (ap· F.P₁ (I.idl f))) ._≅_.to
    ∘ F.γ→ _ .η Fy ∘ F.₁ f .F₁ (F.υ→ .η Fy) ∘ Ff                          ≡⟨ F₁-path (I.idl f) ⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym (idl _) ⟩
    F.₂ (I.idl f) .η Fy ∘ F.γ→ _ .η Fy ∘ F.₁ f .F₁ (F.υ→ .η Fy) ∘ id ∘ Ff ≡⟨ pulll4 (F.right-unit f ηₚ Fy) ∙ idl _ ⟩
    Ff                                                                    ∎
  Fibration .assoc' {x} {y = Fy} {Fz} {f} {g} {h} Ff Fg Fh = Hom-pathp-reflr (F.₀ x) $
    path→iso (ap (λ x → x .F₀ Fz) (ap· F.P₁ (I.assoc f g h))) ._≅_.to
    ∘ F.γ→ _ .η Fz ∘ F.₁ (g I.∘ h) .F₁ Ff ∘ F.γ→ _ .η Fy ∘ F.₁ h .F₁ Fg ∘ Fh
      ≡⟨ F₁-path (I.assoc f g h) ⟩∘⟨refl ⟩
      F.₂ (I.assoc f g h) .η Fz ∘ F.γ→ _ .η Fz
    ∘ F.₁ (g I.∘ h) .F₁ Ff ∘ F.γ→ _ .η Fy ∘ F.₁ h .F₁ Fg ∘ Fh
      ≡⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (sym $ F.γ→ _ .is-natural _ _ _) ∙ introl (F.₁ (g I.∘ h) .F-id) ⟩
      F.₂ (I.assoc f g h) .η Fz ∘ F.γ→ _ .η Fz ∘ F.₁ (g I.∘ h) .F₁ id
    ∘ F.γ→ _ .η (F.₁ f .F₀ Fz) ∘ F.₁ h .F₁ (F.₁ g .F₁ Ff) ∘ F.₁ h .F₁ Fg ∘ Fh
      ≡⟨ pulll4 (F.hexagon h g f ηₚ Fz ∙ ap (F.γ→ _ .η _ ∘_) (idr _ ∙ idr _)) ∙ sym (assoc _ _ _) ⟩
    F.γ→ _ .η Fz ∘ F.₁ h .F₁ (F.γ→ _ .η Fz) ∘ F.₁ h .F₁ (F.₁ g .F₁ Ff) ∘ F.₁ h .F₁ Fg ∘ Fh
      ≡⟨ refl⟩∘⟨ Fr.pulll3 (F.₁ h) refl ⟩
    F.γ→ _ .η Fz ∘ F.₁ h .F₁ (F.γ→ _ .η Fz ∘ F.₁ g .F₁ Ff ∘ Fg) ∘ Fh
      ∎
  Fibration .hom[_] {x} p Ff = F.₂ p .η _ ∘ Ff
  Fibration .coh[_] {x} {y = Fy} p Ff = Hom-pathp-reflr (F.₀ x) $ ap (_∘ Ff) (F₁-path p)

  Grothendieck : Precategory _ _
  Grothendieck = ∫ Fibration
