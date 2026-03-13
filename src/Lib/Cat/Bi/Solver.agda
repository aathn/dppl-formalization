module Lib.Cat.Bi.Solver where

import Lib.Cat.Bi.Reasoning as Br

open import 1Lab.Reflection

open import Cat.Prelude
open import Cat.Bi.Base
import Cat.Solver as Cs
import Cat.Morphism as Cm

module NbE {o ℓ ℓ'} (C : Prebicategory o ℓ ℓ') where

  open Br C
  open Cm._≅_
  open Hom hiding (Hom ; Ob ; id ; _∘_ ; invr ; invl)
  open _=>_

  data Expr₁ : Ob → Ob → Type (o ⊔ ℓ) where
    _↑   : {A B : Ob} → A ↦ B → Expr₁ A B
    `id  : {A : Ob} → Expr₁ A A
    _`⊗_ : {A B C : Ob} → Expr₁ B C → Expr₁ A B → Expr₁ A C

  embed₁ : {A B : Ob} → Expr₁ A B → A ↦ B
  embed₁ (x ↑)    = x
  embed₁ `id      = id
  embed₁ (f `⊗ g) = embed₁ f ⊗ embed₁ g

  instance
    ⟦⟧-Expr₁ : {A B : Ob} → ⟦⟧-notation (Expr₁ A B)
    ⟦⟧-Expr₁ = brackets _ embed₁

  data Expr₂ : {A B : Ob} → Expr₁ A B → Expr₁ A B → Type (o ⊔ ℓ ⊔ ℓ') where
    _↑   : {A B : Ob} {f g : Expr₁ A B} → ⟦ f ⟧ ⇒ ⟦ g ⟧ → Expr₂ f g
    `id  : {A B : Ob} {f : Expr₁ A B} → Expr₂ f f
    _`∘_ : {A B : Ob} {f g h : Expr₁ A B} → Expr₂ g h → Expr₂ f g → Expr₂ f h
    _`◆_
      : {A B C : Ob} {f₁ f₂ : Expr₁ B C} (α : Expr₂ f₁ f₂)
      → {g₁ g₂ : Expr₁ A B} (β : Expr₂ g₁ g₂) → Expr₂ (f₁ `⊗ g₁) (f₂ `⊗ g₂)
    `λ← : {A B : Ob} (f : Expr₁ A B) → Expr₂ (`id `⊗ f) f
    `λ→ : {A B : Ob} (f : Expr₁ A B) → Expr₂ f (`id `⊗ f)
    `ρ← : {A B : Ob} (f : Expr₁ A B) → Expr₂ (f `⊗ `id) f
    `ρ→ : {A B : Ob} (f : Expr₁ A B) → Expr₂ f (f `⊗ `id)
    `α←
      : {A B C D : Ob} (f : Expr₁ C D) (g : Expr₁ B C) (h : Expr₁ A B)
      → Expr₂ (f `⊗ (g `⊗ h)) ((f `⊗ g) `⊗ h)
    `α→
      : {A B C D : Ob} (f : Expr₁ C D) (g : Expr₁ B C) (h : Expr₁ A B)
      → Expr₂ ((f `⊗ g) `⊗ h) (f `⊗ (g `⊗ h))

  infix  50 _↑
  infixr 40 _`∘_
  infixr 30 _`⊗_
  infix 30 _`◆_

  _`▶_
    : {A B C : Ob} (f : Expr₁ B C) {g₁ g₂ : Expr₁ A B}
    → Expr₂ g₁ g₂ → Expr₂ (f `⊗ g₁) (f `⊗ g₂)
  f `▶ β = `id {f = f} `◆ β

  _`◀_
    : {A B C : Ob} {f₁ f₂ : Expr₁ B C}
    → Expr₂ f₁ f₂ → (g : Expr₁ A B) → Expr₂ (f₁ `⊗ g) (f₂ `⊗ g)
  α `◀ g = α `◆ `id {f = g}

  infix 40 _`▶_
  infix 40 _`◀_

  `_ : {A B : Ob} {f g : A ↦ B} → f ⇒ g → Expr₂ (f ↑) (g ↑)
  `_ f = f ↑

  infix 50 `_

  embed₂ : {A B : Ob} {f g : Expr₁ A B} → Expr₂ f g → ⟦ f ⟧ ⇒ ⟦ g ⟧
  embed₂ (x ↑)       = x
  embed₂ `id         = Hom.id
  embed₂ (α `∘ β)    = embed₂ α ∘ embed₂ β
  embed₂ (α `◆ β)    = embed₂ α ◆ embed₂ β
  embed₂ (`λ← f)     = λ← ⟦ f ⟧
  embed₂ (`λ→ f)     = λ→ ⟦ f ⟧
  embed₂ (`ρ← f)     = ρ← ⟦ f ⟧
  embed₂ (`ρ→ f)     = ρ→ ⟦ f ⟧
  embed₂ (`α← f g h) = α← ⟦ f ⟧ ⟦ g ⟧ ⟦ h ⟧
  embed₂ (`α→ f g h) = α→ ⟦ f ⟧ ⟦ g ⟧ ⟦ h ⟧

  instance
    ⟦⟧-Expr₂ : {A B : Ob} {f g : Expr₁ A B} → ⟦⟧-notation (Expr₂ f g)
    ⟦⟧-Expr₂ = brackets _ embed₂

  eval₁ : {A B C : Ob} → Expr₁ B C → A ↦ B → A ↦ C
  eval₁ (f ↑) g    = f ⊗ g
  eval₁ `id f      = f
  eval₁ (f `⊗ g) h = eval₁ f (eval₁ g h)

  nf₁ : {A B : Ob} → Expr₁ A B → A ↦ B
  nf₁ e = eval₁ e id

  eval₁-sound : {A B C : Ob} (e : Expr₁ B C) (f : A ↦ B) → eval₁ e f ≅ ⟦ e ⟧ ⊗ f
  eval₁-sound (f ↑) g    = id-iso
  eval₁-sound `id f      = λ≅
  eval₁-sound (f `⊗ g) h =
    eval₁-sound f (eval₁ g h) ∙Iso
    ▶.F-map-iso (eval₁-sound g h) ∙Iso
    α≅ Iso⁻¹

  nf₁-sound : {A B : Ob} (e : Expr₁ A B) → nf₁ e ≅ ⟦ e ⟧
  nf₁-sound e = eval₁-sound e id ∙Iso ρ≅ Iso⁻¹

  --------------------------------------------------------------------------------
  -- Evaluation

  open Cs.NbE using (`id ; _↑ ; _`∘_)
  module Nf₂ {A} {B} = Cs.NbE (Hom A B)

  Nf₂ : {A B : Ob} → (A ↦ B) → (A ↦ B) → Type (ℓ ⊔ ℓ')
  Nf₂ = Nf₂.Expr

  `whisker
    : {A B C : Ob} (f : Expr₁ B C) {h₁ h₂ : A ↦ B}
    → Nf₂ h₁ h₂ → Nf₂ (eval₁ f h₁) (eval₁ f h₂)
  `whisker `id xs           = xs
  `whisker (f₁ `⊗ f₂) xs    = `whisker f₁ (`whisker f₂ xs)
  `whisker (f ↑) `id        = `id
  `whisker (f ↑) (α ↑)      = (f ▶ α) ↑
  `whisker (f ↑) (xs `∘ ys) = `whisker (f ↑) xs `∘ `whisker (f ↑) ys

  `eval₁-sound-to
    : {A B C : Ob} (g : Expr₁ B C) {f : A ↦ B} → Nf₂ (eval₁ g f) (⟦ g ⟧ ⊗ f)
  `eval₁-sound-to (g ↑)     = `id
  `eval₁-sound-to `id {f}   = λ→ f ↑
  `eval₁-sound-to (g `⊗ g₁) =
    α← _ _ _ ↑ `∘ `eval₁-sound-to g `∘ `whisker g (`eval₁-sound-to g₁)

  `eval₁-sound-from
    : {A B C : Ob} (g : Expr₁ B C) {f : A ↦ B} → Nf₂ (⟦ g ⟧ ⊗ f) (eval₁ g f)
  `eval₁-sound-from (g ↑)     = `id
  `eval₁-sound-from `id {f}   = λ← f ↑
  `eval₁-sound-from (g `⊗ g₁) =
    `whisker g (`eval₁-sound-from g₁) `∘ `eval₁-sound-from g `∘ α→ _ _ _ ↑

  eval₂
    : {A B C : Ob} {g h : Expr₁ B C} {k : A ↦ B}
    → Expr₂ g h → Nf₂ (eval₁ g k) (eval₁ h k)
  eval₂ {g = g} {h} {k} (α ↑) =
    `eval₁-sound-from h `∘ (α ◀ k) ↑ `∘ `eval₁-sound-to g
  eval₂ `id                  = `id
  eval₂ (α `∘ β)             = eval₂ α `∘ eval₂ β
  eval₂ (_`◆_ {f₁ = f₁} α β) = eval₂ α `∘ `whisker f₁ (eval₂ β)
  eval₂ (`λ← _)              = `id
  eval₂ (`λ→ _)              = `id
  eval₂ (`ρ← _)              = `id
  eval₂ (`ρ→ _)              = `id
  eval₂ (`α← _ _ _)          = `id
  eval₂ (`α→ _ _ _)          = `id

  nf₂ : {A B : Ob} {f g : Expr₁ A B} → Expr₂ f g → nf₁ f ⇒ nf₁ g
  nf₂ = Nf₂.nf ⊙ eval₂

  --------------------------------------------------------------------------------
  -- Soundness

  `whisker-sound
    : {A B C : Ob} (f : Expr₁ B C) {h₁ h₂ : A ↦ B} (α : Nf₂ h₁ h₂)
    → eval₁-sound f h₂ .to ∘ ⟦ `whisker f α ⟧ ≡ ⟦ f ⟧ ▶ ⟦ α ⟧ ∘ eval₁-sound f h₁ .to
  `whisker-sound `id xs                    = λ→nat _
  `whisker-sound {A} {_} {C} (f₁ `⊗ f₂) xs =
    eval₁-sound (f₁ `⊗ f₂) _ .to ∘ ⟦ `whisker (f₁ `⊗ f₂) xs ⟧                         ≡⟨ cat! (Hom A C) ⟩
    α← _ _ _ ∘ _ ∘ eval₁-sound f₁ (eval₁ f₂ _) .to ∘ ⟦ `whisker f₁ (`whisker f₂ xs) ⟧ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ `whisker-sound f₁ (`whisker f₂ xs) ⟩
    α← _ _ _ ∘ ⟦ f₁ ⟧ ▶ eval₁-sound f₂ _ .to ∘ ⟦ f₁ ⟧ ▶ ⟦ `whisker f₂ xs ⟧ ∘ _        ≡⟨ refl⟩∘⟨ ▶.extendl (`whisker-sound f₂ xs) ⟩
    α← _ _ _ ∘ ⟦ f₁ ⟧ ▶ (⟦ f₂ ⟧ ▶ ⟦ xs ⟧) ∘ ⟦ f₁ ⟧ ▶ eval₁-sound f₂ _ .to ∘ _         ≡⟨ extendl (▶-assoc .from .is-natural _ _ _) ⟩
    (⟦ f₁ ⟧ ⊗ ⟦ f₂ ⟧) ▶ ⟦ xs ⟧ ∘ α← _ _ _ ∘ ⟦ f₁ ⟧ ▶ eval₁-sound f₂ _ .to ∘ _         ≡⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    (⟦ f₁ ⟧ ⊗ ⟦ f₂ ⟧) ▶ ⟦ xs ⟧ ∘ (α← _ _ _ ∘ ⟦ f₁ ⟧ ▶ eval₁-sound f₂ _ .to) ∘ _       ∎
  `whisker-sound (f ↑) `id        = ▶.intro refl ⟩∘⟨refl
  `whisker-sound (f ↑) (α ↑)      = id-comm-sym
  `whisker-sound (f ↑) (xs `∘ ys) =
    Hom.id ∘ ⟦ `whisker (f ↑) xs ⟧ ∘ ⟦ `whisker (f ↑) ys ⟧ ≡⟨ extendl (`whisker-sound (f ↑) xs) ⟩
    f ▶ ⟦ xs ⟧ ∘ Hom.id ∘ ⟦ `whisker (f ↑) ys ⟧            ≡⟨ refl⟩∘⟨ `whisker-sound (f ↑) ys ⟩
    f ▶ ⟦ xs ⟧ ∘ f ▶ ⟦ ys ⟧ ∘ Hom.id                       ≡⟨ ▶.pulll refl ⟩
    f ▶ (⟦ xs ⟧ ∘ ⟦ ys ⟧) ∘ Hom.id                         ∎

  `eval₁-sound-to-sound
    : {A B C : Ob} (g : Expr₁ B C) {f : A ↦ B}
    → ⟦ `eval₁-sound-to g ⟧ ≡ eval₁-sound g f .to
  `eval₁-sound-to-sound (g ↑)         = refl
  `eval₁-sound-to-sound `id           = refl
  `eval₁-sound-to-sound (g `⊗ g₁) {f} =
    _ ∘ ⟦ `eval₁-sound-to g ⟧ ∘ ⟦ `whisker g (`eval₁-sound-to g₁) ⟧ ≡⟨ refl⟩∘⟨ `eval₁-sound-to-sound g ⟩∘⟨refl ⟩
    _ ∘ eval₁-sound g _ .to ∘ ⟦ `whisker g (`eval₁-sound-to g₁) ⟧   ≡⟨ refl⟩∘⟨ `whisker-sound g (`eval₁-sound-to g₁) ⟩
    _ ∘ ⟦ g ⟧ ▶ ⟦ `eval₁-sound-to g₁ ⟧ ∘ eval₁-sound g _ .to        ≡⟨ pulll (refl⟩∘⟨ ▶.⟨ `eval₁-sound-to-sound g₁ ⟩) ⟩
    eval₁-sound (g `⊗ g₁) f .to                                     ∎

  `eval₁-sound-from-sound
    : {A B C : Ob} (g : Expr₁ B C) {f : A ↦ B}
    → ⟦ `eval₁-sound-from g ⟧ ≡ eval₁-sound g f .from
  `eval₁-sound-from-sound (g ↑)         = refl
  `eval₁-sound-from-sound `id           = refl
  `eval₁-sound-from-sound (g `⊗ g₁) {f} =
    ⟦ `whisker g (`eval₁-sound-from g₁) ⟧ ∘ ⟦ `eval₁-sound-from g ⟧ ∘ _ ≡⟨ refl⟩∘⟨ `eval₁-sound-from-sound g ⟩∘⟨refl ⟩
    ⟦ `whisker g (`eval₁-sound-from g₁) ⟧ ∘ eval₁-sound g _ .from ∘ _   ≡⟨ extendl `whisker-sound' ⟩
    eval₁-sound g _ .from ∘ ⟦ g ⟧ ▶ ⟦ `eval₁-sound-from g₁ ⟧ ∘ _        ≡⟨ refl⟩∘⟨ ▶.⟨ `eval₁-sound-from-sound g₁ ⟩ ⟩∘⟨refl ⟩
    eval₁-sound (g `⊗ g₁) f .from                                       ∎
    where `whisker-sound' = sym $ swizzle
            (sym $ `whisker-sound g (`eval₁-sound-from g₁))
            (eval₁-sound g _ .invl) (eval₁-sound g _ .invr)

  eval₂-sound
    : {A B C : Ob} {g h : Expr₁ B C} (α : Expr₂ g h) {k : A ↦ B}
    → eval₁-sound h k .to ∘ ⟦ eval₂ α ⟧ ≡ ⟦ α ⟧ ◀ k ∘ eval₁-sound g k .to
  eval₂-sound {g = g} {h} (α ↑) {k} =
    eval₁-sound h k .to ∘ ⟦ `eval₁-sound-from h ⟧ ∘ α ◀ k ∘ ⟦ `eval₁-sound-to g ⟧ ≡⟨ refl⟩∘⟨ `eval₁-sound-from-sound h ⟩∘⟨refl ⟩
    eval₁-sound h k .to ∘ eval₁-sound h k .from ∘ α ◀ k ∘ ⟦ `eval₁-sound-to g ⟧   ≡⟨ cancell (eval₁-sound h _ .invl) ⟩
    α ◀ k ∘ ⟦ `eval₁-sound-to g ⟧                                                 ≡⟨ refl⟩∘⟨ `eval₁-sound-to-sound g ⟩
    (α ◀ k) ∘ eval₁-sound g k .to                                                 ∎
  eval₂-sound `id                            = idr _ ∙ ◀.introl refl
  eval₂-sound (_`∘_ {f = f} {g} {h} α β) {k} =
    eval₁-sound h k .to ∘ ⟦ eval₂ α ⟧ ∘ ⟦ eval₂ β ⟧ ≡⟨ extendl (eval₂-sound α) ⟩
    ⟦ α ⟧ ◀ k ∘ eval₁-sound g k .to ∘ ⟦ eval₂ β ⟧   ≡⟨ refl⟩∘⟨ eval₂-sound β ⟩
    ⟦ α ⟧ ◀ k ∘ ⟦ β ⟧ ◀ k ∘ eval₁-sound f k .to     ≡⟨ ◀.pulll refl ⟩
    (⟦ α ⟧ ∘ ⟦ β ⟧) ◀ k ∘ eval₁-sound f k .to       ∎
  eval₂-sound {A} {_} {C} (_`◆_ {f₁ = f₁} {f₂} α {g₁} {g₂} β) {k} =
    eval₁-sound (f₂ `⊗ g₂) k .to ∘ ⟦ eval₂ α ⟧ ∘ ⟦ `whisker f₁ (eval₂ β) ⟧            ≡⟨ cat! (Hom A C) ⟩
    _ ∘ _ ∘ eval₁-sound f₂ (eval₁ g₂ k) .to ∘ ⟦ eval₂ α ⟧ ∘ ⟦ `whisker f₁ (eval₂ β) ⟧ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (eval₂-sound α) ∙ ap (⟦ α ⟧ ◀ _ ∘_) (`whisker-sound f₁ (eval₂ β)) ⟩
    _ ∘ ⟦ f₂ ⟧ ▶ eval₁-sound g₂ k .to ∘ ⟦ α ⟧ ◀ eval₁ g₂ k ∘ ⟦ f₁ ⟧ ▶ ⟦ eval₂ β ⟧ ∘ _ ≡⟨ refl⟩∘⟨ ⊗.extendl (id-comm-sym ,ₚ id-comm) ⟩
    _ ∘ _ ∘ ⟦ f₁ ⟧ ▶ eval₁-sound g₂ k .to ∘ ⟦ f₁ ⟧ ▶ ⟦ eval₂ β ⟧ ∘ _                  ≡⟨ refl⟩∘⟨ refl⟩∘⟨ ▶.extendl (eval₂-sound β) ⟩
    α← _ _ _ ∘ ⟦ α ⟧ ◀ (⟦ g₂ ⟧ ⊗ k) ∘ ⟦ f₁ ⟧ ▶ (⟦ β ⟧ ◀ k) ∘ _                        ≡⟨ extendl (◀-assoc .to .is-natural _ _ _) ⟩
    (⟦ α ⟧ ◀ ⟦ g₂ ⟧) ◀ k ∘ α← _ _ _ ∘ ⟦ f₁ ⟧ ▶ (⟦ β ⟧ ◀ k) ∘ _                        ≡⟨ refl⟩∘⟨ extendl (◀-▶-comm .from .is-natural _ _ _) ⟩
    (⟦ α ⟧ ◀ ⟦ g₂ ⟧) ◀ k ∘ (⟦ f₁ ⟧ ▶ ⟦ β ⟧) ◀ k ∘ α← _ _ _ ∘ _                        ≡⟨ ◀.pulll (⊗.collapse (idr _ ,ₚ idl _)) ⟩
    (⟦ α ⟧ ◆ ⟦ β ⟧) ◀ k ∘ α← _ _ _ ∘ _                                                ≡⟨ refl ⟩∘⟨ assoc _ _ _ ⟩
    (⟦ α ⟧ ◆ ⟦ β ⟧) ◀ k ∘ eval₁-sound (f₁ `⊗ g₁) k .to                                ∎
  eval₂-sound (`λ← f) {k} =
    eval₁-sound f k .to ∘ Hom.id                          ≡⟨ idr _ ∙ intror (λ≅ .invr) ∙ extendl (sym $ λ←nat _) ⟩
    λ← _ ∘ id ▶ eval₁-sound f k .to ∘ λ→ _                ≡⟨ pushl (sym (rswizzle (sym triangle-λ←) (α≅ .invl))) ⟩
    λ← _ ◀ k ∘ α← _ _ _ ∘ id ▶ eval₁-sound f k .to ∘ λ→ _ ≡⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    λ← _ ◀ k ∘ eval₁-sound (`id `⊗ f) k .to               ∎
  eval₂-sound (`λ→ f) {k} =
    eval₁-sound (`id `⊗ f) k .to ∘ Hom.id   ≡⟨ idr _ ∙ extendr (sym $ λ→nat _) ⟩
    (α← _ _ _ ∘ λ→ _) ∘ eval₁-sound f k .to ≡⟨ lswizzle triangle-λ→ (α≅ .invr) ⟩∘⟨refl ⟩
    λ→ _ ◀ k ∘ eval₁-sound f k .to          ∎
  eval₂-sound (`ρ← f) =
    idr _ ∙ insertl (pulll (triangle _ _) ∙ ▶.annihilate (λ≅ .invr))
  eval₂-sound (`ρ→ f) {k} = idr _ ∙ ap (_∘ eval₁-sound f k .to) triangle-inv
  eval₂-sound {A} {_} {C} (`α← f g h) {k} =
    eval₁-sound ((f `⊗ g) `⊗ h) k .to ∘ Hom.id                                       ≡⟨ cat! (Hom A C) ⟩
    α← _ _ _ ∘ (⟦ f ⟧ ⊗ ⟦ g ⟧) ▶ eval₁-sound h k .to ∘ α← _ _ _ ∘ _                  ≡⟨ refl⟩∘⟨ extendl (sym $ ▶-assoc .from .is-natural _ _ _) ⟩
    α← _ _ _ ∘ α← _ _ _ ∘ ⟦ f ⟧ ▶ (⟦ g ⟧ ▶ eval₁-sound h k .to) ∘ _                  ≡⟨ extendl (sym $ pentagon _ _ _ _) ⟩
    α← _ _ _ ◀ k ∘ (α← _ _ _ ∘ ⟦ f ⟧ ▶ α← _ _ _) ∘ ⟦ f ⟧ ▶ _ ∘ ⟦ f ⟧ ▶ _ ∘ _         ≡˘⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    _ ∘ _ ∘ ⟦ f ⟧ ▶ α← _ _ _ ∘ ⟦ f ⟧ ▶ (⟦ g ⟧ ▶ eval₁-sound h k .to) ∘ ⟦ f ⟧ ▶ _ ∘ _ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ ▶.pulll refl ∙ ▶.pulll refl ⟩
    α← _ _ _ ◀ k ∘ α← _ _ _ ∘ ⟦ f ⟧ ▶ _ ∘ _                                          ≡⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    α← _ _ _ ◀ k ∘ eval₁-sound (f `⊗ g `⊗ h) k .to                                   ∎
  eval₂-sound {A} {_} {C} (`α→ f g h) {k} =
    eval₁-sound (f `⊗ (g `⊗ h)) k .to ∘ Hom.id                                       ≡⟨ cat! (Hom A C) ⟩
    α← _ _ _ ∘ ⟦ f ⟧ ▶ ((α← _ _ _ ∘ ⟦ g ⟧ ▶ eval₁-sound h k .to) ∘ _) ∘ _            ≡⟨ refl⟩∘⟨ ▶.pushl refl ∙ ▶.pushl refl ⟩
    α← _ _ _ ∘ ⟦ f ⟧ ▶ α← _ _ _ ∘ ⟦ f ⟧ ▶ (⟦ g ⟧ ▶ eval₁-sound h k .to) ∘ _          ≡⟨ extendl (sym $ lswizzle (sym $ pentagon _ _ _ _) (◀.annihilate (α≅ .invl))) ⟩
    α→ _ _ _ ◀ k ∘ (α← _ _ _ ∘ α← _ _ _) ∘ ⟦ f ⟧ ▶ (⟦ g ⟧ ▶ eval₁-sound h k .to) ∘ _ ≡˘⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    α→ _ _ _ ◀ k ∘ α← _ _ _ ∘ α← _ _ _ ∘ ⟦ f ⟧ ▶ (⟦ g ⟧ ▶ eval₁-sound h k .to) ∘ _   ≡⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (▶-assoc .from .is-natural _ _ _) ⟩
    α→ _ _ _ ◀ k ∘ α← _ _ _ ∘ (⟦ f ⟧ ⊗ ⟦ g ⟧) ▶ eval₁-sound h k .to ∘ α← _ _ _ ∘ _   ≡⟨ cat! (Hom A C) ⟩
    α→ _ _ _ ◀ k ∘ eval₁-sound ((f `⊗ g) `⊗ h) k .to                                 ∎

  nf₂-sound
    : {A B : Ob} {f g : Expr₁ A B} (α : Expr₂ f g)
    → nf₁-sound g .to ∘ nf₂ α ≡ ⟦ α ⟧ ∘ nf₁-sound f .to
  nf₂-sound {A} {B} {f} {g} α =
    nf₁-sound g .to ∘ nf₂ α                      ≡⟨ refl⟩∘⟨ Nf₂.eval-sound (eval₂ α) ⟩
    nf₁-sound g .to ∘ ⟦ eval₂ α ⟧                ≡⟨ extendr (eval₂-sound α) ∙ sym (assoc _ _ _) ⟩
    ρ← ⟦ g ⟧ ∘ ⟦ α ⟧ ◀ id ∘ eval₁-sound f id .to ≡⟨ extendl (ρ←nat _) ⟩
    ⟦ α ⟧ ∘ nf₁-sound f .to                      ∎

  abstract
    solve : {A B : Ob} {f g : Expr₁ A B} (α β : Expr₂ f g) → nf₂ α ≡ nf₂ β → ⟦ α ⟧ ≡ ⟦ β ⟧
    solve {f = f} {g} α β p =
      iso→epic (nf₁-sound f) _ _ $
      sym (nf₂-sound α) ∙ ap (nf₁-sound g .to ∘_) p ∙ nf₂-sound β


module Reflection where

  pattern category-args C xs      = _ hm∷ _ hm∷ C v∷ xs
  pattern bicategory-args C xs    = _ hm∷ _ hm∷ _ hm∷ C v∷ xs
  pattern functor-args functor xs =
    _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ functor v∷ xs
  pattern iso-args f xs = _ hm∷ _ hm∷ _ h∷ _ h∷ _ h∷ f v∷ xs
  pattern nt-args nt xs = _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ h∷ _ h∷ nt v∷ xs

  pattern “F₀” functor x =
    def (quote Functor.F₀) (functor-args functor (x v∷ []))

  pattern “F₁” functor x y f =
    def (quote Functor.F₁) (functor-args functor (x h∷ y h∷ f v∷ []))

  pattern “,” x y =
    con (quote _,_) (_ hm∷ _ hm∷ _ h∷ _ h∷ x v∷ y v∷ [])

  pattern “id₁” =
    def (quote Prebicategory.id) (bicategory-args _ (_ h∷ []))

  pattern “compose” =
    (def (quote Prebicategory.compose) (bicategory-args _ (_ h∷ _ h∷ _ h∷ [])))

  pattern “unitor-l” =
    (def (quote Prebicategory.unitor-l) (bicategory-args _ (_ h∷ _ h∷ [])))

  pattern “unitor-r” =
    (def (quote Prebicategory.unitor-r) (bicategory-args _ (_ h∷ _ h∷ [])))

  pattern “associator” =
    (def (quote Prebicategory.associator) (bicategory-args _ (_ h∷ _ h∷ _ h∷ _ h∷ [])))

  pattern “to” f =
    (def (quote Cm._≅_.to) (iso-args f []))

  pattern “from” f =
    (def (quote Cm._≅_.from) (iso-args f []))

  pattern “η” f x =
    (def (quote _=>_.η) (nt-args f (x v∷ [])))

  pattern “⊗” f g = “F₀” “compose” (“,” f g)

  pattern “Hom” =
    (def (quote Prebicategory.Hom) (bicategory-args _ (_ v∷ _ v∷ [])))

  pattern “id₂” f =
    def (quote Precategory.id) (category-args “Hom” (f h∷ []))

  pattern “∘” f g h α β =
    def (quote Precategory._∘_) (category-args “Hom” (f h∷ g h∷ h h∷ α v∷ β v∷ []))

  pattern “◆” f₁ f₂ α g₁ g₂ β = “F₁” “compose” (“,” f₁ g₁) (“,” f₂ g₂) (“,” α β)

  pattern “λ←” f     = “η” (“from” “unitor-l”) f
  pattern “λ→” f     = “η” (“to” “unitor-l”) f
  pattern “ρ←” f     = “η” (“from” “unitor-r”) f
  pattern “ρ→” f     = “η” (“to” “unitor-r”) f
  pattern “α←” f g h = “η” (“from” “associator”) (“,” f (“,” g h))
  pattern “α→” f g h = “η” (“to” “associator”) (“,” f (“,” g h))

  mk-hom-args : Term → List (Arg Term) → List (Arg Term)
  mk-hom-args cat xs = infer-hidden 3 $ cat h∷ infer-hidden 2 xs

  “solve” : Term → Term → Term → Term
  “solve” cat lhs rhs =
    def (quote NbE.solve) (cat v∷ lhs v∷ rhs v∷ def (quote refl) [] v∷ [])

  “nf₂” : Term → Term → Term
  “nf₂” cat α = def (quote NbE.nf₂) (cat v∷ α v∷ [])

  build-expr₁ : Term → Term
  build-expr₁ “id₁”     = con (quote NbE.Expr₁.`id) []
  build-expr₁ (“⊗” f g) = con (quote NbE.Expr₁._`⊗_) (ef v∷ eg v∷ []) where
    ef = build-expr₁ f
    eg = build-expr₁ g
  build-expr₁ f = con (quote NbE.Expr₁._↑) (f v∷ [])

  build-expr₂ : Term → Term → Term → Term → Term
  build-expr₂ cat = build where
    build-unitor : Name → Term → Term
    build-unitor n f = con n (ef v∷ []) where
      ef = build-expr₁ f
    build-associator : Name → Term → Term → Term → Term
    build-associator n f g h = con n (ef v∷ eg v∷ eh v∷ []) where
      ef = build-expr₁ f
      eg = build-expr₁ g
      eh = build-expr₁ h

    build : Term → Term → Term → Term
    build _ _ (“id₂” f) = con (quote NbE.Expr₂.`id) (mk-hom-args cat (ef h∷ [])) where
      ef = build-expr₁ f
    build _ _ (“∘” f g h α β) = con (quote NbE.Expr₂._`∘_) (eα v∷ eβ v∷ []) where
      eα = build-expr₂ cat g h α
      eβ = build-expr₂ cat f g β
    build _ _ (“◆” f₁ f₂ α g₁ g₂ β) = con (quote NbE.Expr₂._`◆_) (eα v∷ eβ v∷ []) where
      eα = build-expr₂ cat f₁ f₂ α
      eβ = build-expr₂ cat g₁ g₂ β
    build _ _ (“λ←” f)     = build-unitor (quote NbE.Expr₂.`λ←) f
    build _ _ (“λ→” f)     = build-unitor (quote NbE.Expr₂.`λ→) f
    build _ _ (“ρ←” f)     = build-unitor (quote NbE.Expr₂.`ρ←) f
    build _ _ (“ρ→” f)     = build-unitor (quote NbE.Expr₂.`ρ→) f
    build _ _ (“α←” f g h) = build-associator (quote NbE.Expr₂.`α←) f g h
    build _ _ (“α→” f g h) = build-associator (quote NbE.Expr₂.`α→) f g h
    build f g α            = con (quote NbE.Expr₂._↑) args where
      ef = build-expr₁ f
      eg = build-expr₁ g
      args = mk-hom-args cat (ef h∷ eg h∷ α v∷ [])

  dont-reduce : List Name
  dont-reduce =
    [ quote Prebicategory.id
    , quote Prebicategory.compose
    , quote Prebicategory.unitor-l
    , quote Prebicategory.unitor-r
    , quote Prebicategory.associator
    , quote Prebicategory.Hom
    ]

module _ {o ℓ ℓ'} (C : Prebicategory o ℓ ℓ') where
  open Reflection
  open Prebicategory C
  module _ {A B : Ob} {f g : A ↦ B} {α β : f ⇒ g} where
    private
      bicat-worker : Term → TC ⊤
      bicat-worker hole =
        withNormalisation true $
        withReduceDefs (false , dont-reduce) $ do
        `α ← wait-for-type =<< quoteTC α
        `β ← quoteTC β
        `f ← quoteTC f
        `g ← quoteTC g
        `C ← quoteTC C
        noConstraints $ unify hole
          $ “solve” `C (build-expr₂ `C `f `g `α) (build-expr₂ `C `f `g `β)

    bicat-wrapper : {@(tactic bicat-worker) p : α ≡ β} → α ≡ β
    bicat-wrapper {p = p} = p

macro
  bicat! : Term → Term → TC ⊤
  bicat! c = flip unify (def (quote bicat-wrapper) (c v∷ []))

private module _ {o ℓ ℓ'} {C : Prebicategory o ℓ ℓ'} where
  open Br C
  variable
    A B : Ob
    f g h i : A ↦ B
    α β γ δ : f ⇒ g

  test-distrib-▶ : f ▶ (α ∘ β) ≡ f ▶ α ∘ f ▶ β
  test-distrib-▶ = bicat! C

  test-distrib-◀ : (α ∘ β) ◀ f ≡ α ◀ f ∘ β ◀ f
  test-distrib-◀ = bicat! C

  test-pentagon-α→
    : (f ▶ α→ g h i) ∘ α→ f (g ⊗ h) i ∘ (α→ f g h ◀ i)
    ≡ α→ f g (h ⊗ i) ∘ α→ (f ⊗ g) h i
  test-pentagon-α→ = bicat! C

  test-triangle-ρ← : ρ← (f ⊗ g) ∘ α← f g id ≡ f ▶ ρ← g
  test-triangle-ρ← = bicat! C

  test-triangle-λ← : λ← (f ⊗ g) ∘ α→ id f g ≡ λ← f ◀ g
  test-triangle-λ← = bicat! C

  -- TODO: Use Reflection.Variables to introduce an ordering on leaf nodes so that
  -- we can solve goals involving interchange
  -- test-interchange : (α ∘ β) ◆ (γ ∘ δ) ≡ (α ◆ γ) ∘ (β ◆ δ)
  -- test-interchange = bicat! C
