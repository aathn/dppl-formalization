import Lib.Cat.Bi.Reasoning as Br

open import Cat.Prelude
open import Cat.Bi.Base

module Lib.Cat.Bi.Solver {o ℓ ℓ'} (C : Prebicategory o ℓ ℓ') where
  open Br C
  open Hom._≅_

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
      : {A B C : Ob} {f₁ f₂ : Expr₁ B C} {g₁ g₂ : Expr₁ A B}
      → Expr₂ f₁ f₂ → Expr₂ g₁ g₂ → Expr₂ (f₁ `⊗ g₁) (f₂ `⊗ g₂)
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
  infixr 30 _`⊗_
  infix  30 _`◆_
  infixr 30 _`∘_

  _`▶_
    : {A B C : Ob} (f : Expr₁ B C) {g₁ g₂ : Expr₁ A B}
    → Expr₂ g₁ g₂ → Expr₂ (f `⊗ g₁) (f `⊗ g₂)
  f `▶ α = `id `◆ α

  _`◀_
    : {A B C : Ob} {f₁ f₂ : Expr₁ B C}
    → Expr₂ f₁ f₂ → (g : Expr₁ A B) → Expr₂ (f₁ `⊗ g) (f₂ `⊗ g)
  α `◀ g = α `◆ `id

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

  eval₁-sound : {A B C : Ob} (e : Expr₁ B C) (f : A ↦ B) → eval₁ e f Hom.≅ ⟦ e ⟧ ⊗ f
  eval₁-sound (f ↑) g    = Hom.id-iso
  eval₁-sound `id f      = λ≅
  eval₁-sound (f `⊗ g) h =
    eval₁-sound f (eval₁ g h) Hom.∙Iso
    ▶.F-map-iso (eval₁-sound g h) Hom.∙Iso
    α≅ Hom.Iso⁻¹

  nf₁-sound : {A B : Ob} (e : Expr₁ A B) → nf₁ e Hom.≅ ⟦ e ⟧
  nf₁-sound e = eval₁-sound e id Hom.∙Iso ρ≅ Hom.Iso⁻¹

  data Nf₂ {A B : Ob} : (f g : A ↦ B) → Type (o ⊔ ℓ ⊔ ℓ') where
    idN  : {f : A ↦ B} → Nf₂ f f
    _∘N_ : {f g h : A ↦ B} → (g ⇒ h) → Nf₂ f g → Nf₂ f h

  Nf₂-comp : {A B : Ob} {f g h : A ↦ B} → Nf₂ g h → Nf₂ f g → Nf₂ f h
  Nf₂-comp idN       ys = ys
  Nf₂-comp (x ∘N xs) ys = x ∘N Nf₂-comp xs ys

  Nf₂-whisker
    : {A B C : Ob} {g : Expr₁ B C} {h₁ h₂ : A ↦ B}
    → Nf₂ h₁ h₂ → Nf₂ (eval₁ g h₁) (eval₁ g h₂)
  Nf₂-whisker idN                 = idN
  Nf₂-whisker {g = g ↑} (α ∘N xs) = (g ▶ α) ∘N Nf₂-whisker {g = g ↑} xs
  Nf₂-whisker {g = `id} xs        = xs
  Nf₂-whisker {g = g₁ `⊗ g₂} xs   = Nf₂-whisker {g = g₁} (Nf₂-whisker {g = g₂} xs)

  eval₂
    : {A B C : Ob} {f : A ↦ C} {g h : Expr₁ B C} {k : A ↦ B}
    → Expr₂ g h → Nf₂ f (eval₁ g k) → Nf₂ f (eval₁ h k)
  eval₂ {g = g} {h} {k} (α ↑) γ  = (eval₁-sound h k .from ∘ α ◀ k ∘ eval₁-sound g k .to) ∘N γ
  eval₂ `id γ                    = γ
  eval₂ (α `∘ β) γ               = eval₂ α (eval₂ β γ)
  eval₂ {g = g₁ `⊗ _} (α `◆ β) γ =
    eval₂ α (Nf₂-comp (Nf₂-whisker {g = g₁} (eval₂ β idN)) γ)
  eval₂ (`λ← f) γ     = γ
  eval₂ (`λ→ f) γ     = γ
  eval₂ (`ρ← f) γ     = γ
  eval₂ (`ρ→ f) γ     = γ
  eval₂ (`α← f g h) γ = γ
  eval₂ (`α→ f g h) γ = γ

  extract : {A B : Ob} {f g : A ↦ B} → Nf₂ f g → f ⇒ g
  extract idN       = Hom.id
  extract (x ∘N xs) = x ∘ extract xs

  nf₂ : {A B : Ob} {f g : Expr₁ A B} → Expr₂ f g → nf₁ f ⇒ nf₁ g
  nf₂ α = extract (eval₂ α idN)

  postulate
    eval₂-sound
      : {A B C : Ob} {f : A ↦ C} {g h : Expr₁ B C} {k : A ↦ B}
      → (α : Expr₂ g h) (γ : Nf₂ f (eval₁ g k))
      → extract (eval₂ α γ) ≡ eval₁-sound h k .from ∘ ⟦ α ⟧ ◀ k ∘ eval₁-sound g k .to ∘ extract γ
  -- eval₂-sound (` x) γ = {!!}
  -- eval₂-sound {g = g} `id γ = {!!}
  -- eval₂-sound (α `∘ β) γ = {!!}
  -- eval₂-sound (α `◆ β) γ = {!!}
  -- eval₂-sound (`λ← f) γ = {!!}
  -- eval₂-sound (`λ→ f) γ = {!!}
  -- eval₂-sound (`ρ← f) γ = {!!}
  -- eval₂-sound (`ρ→ f) γ = {!!}
  -- eval₂-sound (`α← f g h) γ = {!!}
  -- eval₂-sound (`α→ f g h) γ = {!!}

  nf₂-sound
    : {A B : Ob} {f g : Expr₁ A B} (α : Expr₂ f g)
    → nf₂ α ≡ nf₁-sound g .from ∘ ⟦ α ⟧ ∘ nf₁-sound f .to
  nf₂-sound {A} {B} {f} {g} α =
    nf₂ α                                                                         ≡⟨ eval₂-sound α idN ⟩
    eval₁-sound g id .from ∘ ⟦ α ⟧ ◀ id ∘ eval₁-sound f id .to ∘ Hom.id           ≡⟨ refl⟩∘⟨ ap₂ _∘_ (Hom.intror (ρ≅ .invl) ∙ Hom.extendl (sym $ ρ→nat _)) (idr _) ⟩
    eval₁-sound g id .from ∘ (ρ→ ⟦ g ⟧ ∘ ⟦ α ⟧ ∘ ρ← ⟦ f ⟧) ∘ eval₁-sound f id .to ≡⟨ cat! (Hom A B) ⟩
    (eval₁-sound g id .from ∘ ρ→ ⟦ g ⟧) ∘ ⟦ α ⟧ ∘ ρ← ⟦ f ⟧ ∘ eval₁-sound f id .to ∎
    where open Hom using (refl⟩∘⟨_ ; idr)

  abstract
    solve : {A B : Ob} {f g : Expr₁ A B} (α β : Expr₂ f g) → nf₂ α ≡ nf₂ β → ⟦ α ⟧ ≡ ⟦ β ⟧
    solve {f = f} {g} α β p =
      Hom.iso→epic (nf₁-sound f) _ _ $
      Hom.iso→monic (nf₁-sound g Hom.Iso⁻¹) _ _ $
      sym (nf₂-sound α) ∙ p ∙ nf₂-sound β

  -- test-distrib-◁ : {A B C : Ob} {f : B ↦ C} {g h i : A ↦ B}
  --                  (α : h ⇒ i) (β : g ⇒ h) → Type _
  -- test-distrib-◁ {f = f} α β =
  --   let
  --     LHS = `id {f = f ↑} `◆ (` α `∘ ` β)
  --     RHS = (`id {f = f ↑} `◆ ` α) `∘ (`id {f = f ↑} `◆ ` β)
  --   in nf₂ LHS ≡ nf₂ RHS

  -- check-distrib-◁ : ∀ {A B C f g h i} α β → test-distrib-◁ {A}{B}{C}{f}{g}{h}{i} α β
  -- check-distrib-◁ α β = refl

  -- test-distrib-▷ : {A B C : Ob} {f : A ↦ B} {g h i : B ↦ C}
  --                  (α : h ⇒ i) (β : g ⇒ h) → Type _
  -- test-distrib-▷ {f = f} α β =
  --   let
  --     LHS = (` α `∘ ` β) `◆ `id {f = f ↑}
  --     RHS = (` α `◆ `id {f = f ↑}) `∘ (` β `◆ `id {f = f ↑})
  --   in nf₂ LHS ≡ nf₂ RHS

  -- check-distrib-▷ : ∀ {A B C f g h i} α β → test-distrib-▷ {A}{B}{C}{f}{g}{h}{i} α β
  -- check-distrib-▷ α β = refl

  -- test-ghost-whiskering : {A B C D E : Ob}
  --                         (f : C ↦ D) (g : B ↦ C) (h : A ↦ B) (i : E ↦ A) → Type _
  -- test-ghost-whiskering f g h i =
  --   let
  --     ghost-expr = `id {f = f ↑} `◆ `α→ (g ↑) (h ↑) (i ↑)
  --   in
  --     nf₂ ghost-expr ≡ nf₂ {g = f ↑ `⊗ (g ↑ `⊗ h ↑) `⊗ i ↑} `id

  -- check-ghost : ∀ {A B C D E} f g h i → test-ghost-whiskering {A}{B}{C}{D}{E} f g h i
  -- check-ghost f g h i = refl
