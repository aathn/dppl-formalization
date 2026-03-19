open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Solver

open import Lib.Cat.Bi.Lax-transfor

import Cat.Bi.Reasoning as Br

module Lib.Cat.Bi.Modification where

private variable
  o o' h h' ℓ ℓ' : Level
  B C : Prebicategory o h ℓ

unquoteDecl H-Level-Modification = declare-record-hlevel 2 H-Level-Modification (quote Modification)

open Lax-transfor
open Modification

module _
  {B : Prebicategory o h ℓ} {C : Prebicategory o' h' ℓ'} {F G : Lax-functor B C} where
  open Prebicategory C
  private
    module B  = Prebicategory B
    module C  = Br C
    module CH = C.Hom
    module F  = Lax-functor F
    module G  = Lax-functor G

  idmd : {α : F =>ₗ G} → Modification α α
  idmd .Γ _        = Hom.id
  idmd .is-natural = C.⊗.elimr refl ∙ C.⊗.introl refl

  _∘md_ : {α β γ : F =>ₗ G} → Modification β γ → Modification α β → Modification α γ
  _∘md_ f g .Γ a                                    = f .Γ a ∘ g .Γ a
  _∘md_ {x} {y} {z} f g .is-natural {a} {b} {f = h} =
    ν→ z h ∘ G.₁ h ▶ (f .Γ a ∘ g .Γ a)       ≡⟨ CH.refl⟩∘⟨ C.▶-distribr ⟩
    ν→ z h ∘ G.₁ h ▶ f .Γ a ∘ G.₁ h ▶ g .Γ a ≡⟨ CH.extendl $ f .is-natural ⟩
    f .Γ b ◀ F.₁ h ∘ ν→ y h ∘ G.₁ h ▶ g .Γ a ≡⟨ CH.refl⟩∘⟨ g .is-natural ⟩
    f .Γ b ◀ F.₁ h ∘ g .Γ b ◀ F.₁ h ∘ ν→ x h ≡⟨ CH.pulll $ sym C.◀-distribl ⟩
    (f .Γ b ∘ g .Γ b) ◀ F.₁ h ∘ ν→ x h       ∎

  opaque
    Mod-is-set : {α β : F =>ₗ G} → is-set (Modification α β)
    Mod-is-set = hlevel 2

  Mod-pathp : {α α' β β' : F =>ₗ G}
            → (p : α ≡ α') (q : β ≡ β')
            → {a : Modification α β} {b : Modification α' β'}
            → (∀ x → PathP _ (a .Γ x) (b .Γ x))
            → PathP (λ i → Modification (p i) (q i)) a b
  Mod-pathp p q path i .Γ x                            = path x i
  Mod-pathp p q {a} {b} path i .is-natural {x} {y} {f} =
    is-prop→pathp
      (λ i → CH.Hom-set _ _
        (ν→ (q i) f ∘ G.₁ f ▶ path x i) (path y i ◀ F.₁ f ∘ ν→ (p i) f))
      (a .is-natural)
      (b .is-natural) i
  
  Mod-path : {α β : F =>ₗ G} {a b : Modification α β}
           → ((x : _) → a .Γ x ≡ b .Γ x)
           → a ≡ b
  Mod-path = Mod-pathp refl refl
  
  _Γᵈ_ : {α α' β β' : F =>ₗ G} {p : α ≡ α'} {q : β ≡ β'}
       → {a : Modification α β} {b : Modification α' β'}
       → PathP (λ i → Modification (p i) (q i)) a b
       → ∀ x → PathP _ (a .Γ x) (b .Γ x)
  p Γᵈ x = apd (λ i e → e .Γ x) p
  
  _Γₚ_ : {α β : F =>ₗ G} {a b : Modification α β} → a ≡ b → ∀ x → a .Γ x ≡ b .Γ x
  p Γₚ x = ap (λ e → e .Γ x) p
  
  infixl 45 _Γₚ_
  
  instance
    Extensional-modification
      : ∀ {ℓr} {α β : F =>ₗ G}
      → ⦃ sa : {x : B.Ob} → Extensional (α .σ x ⇒ β .σ x) ℓr ⦄
      → Extensional (Modification α β) (o ⊔ ℓr)
    Extensional-modification ⦃ sa ⦄ .Pathᵉ f g = ∀ i → Pathᵉ sa (f .Γ i) (g .Γ i)
    Extensional-modification ⦃ sa ⦄ .reflᵉ x i = reflᵉ sa (x .Γ i)
    Extensional-modification ⦃ sa ⦄ .idsᵉ .to-path x = Mod-path λ i →
      sa .idsᵉ .to-path (x i)
    Extensional-modification ⦃ sa ⦄ .idsᵉ .to-path-over h =
      is-prop→pathp (λ i → Π-is-hlevel 1 λ _ → Pathᵉ-is-hlevel 1 sa (hlevel 2)) _ _

_◆md_
  : {F G H : Lax-functor B C} {α α' : G =>ₗ H} {β β' : F =>ₗ G}
  → Modification α α' → Modification β β' → Modification (α ∘lx β) (α' ∘lx β')
_◆md_ {C = C} {F} {G} {H} {α} {α'} {β} {β'} f g = md where
  module C  = Prebicategory C
  module F  = Lax-functor F
  module G  = Lax-functor G
  module H  = Lax-functor H
  module α  = Lax-transfor α
  module α' = Lax-transfor α'
  module β  = Lax-transfor β
  module β' = Lax-transfor β'
  module f  = Modification f
  module g  = Modification g
  md : Modification _ _
  md .Γ x                    = f .Γ x C.◆ g .Γ x
  md .is-natural {a} {b} {x} =
        (C.α← _ C.∘ α'.σ b C.▶ β'.ν→ x C.∘ C.α→ _ C.∘ α'.ν→ x C.◀ β'.σ a C.∘ C.α← _)
    C.∘ H.₁ x C.▶ (f.Γ a C.◆ g.Γ a)
      ≡⟨ bicat! C ⟩
        C.α← _ C.∘ α'.σ b C.▶ β'.ν→ x C.∘ C.α→ _ C.∘ ⌜ α'.ν→ x C.∘ H.₁ x C.▶ f.Γ a ⌝ C.◀ β'.σ a
    C.∘ C.α← _ C.∘ H.₁ x C.▶ (α.σ a C.▶ g.Γ a)
      ≡⟨ ap! f.is-natural ⟩
        C.α← _ C.∘ α'.σ b C.▶ β'.ν→ x C.∘ C.α→ _ C.∘ (f.Γ b C.◀ G.₁ x C.∘ α.ν→ x) C.◀ β'.σ a
    C.∘ C.α← _ C.∘ H.₁ x C.▶ (α.σ a C.▶ g.Γ a)
      ≡⟨ bicat! C ⟩
        C.α← _ C.∘ f.Γ b C.◀ (β'.σ b C.⊗ F.₁ x)
    C.∘ α.σ b C.▶ ⌜ β'.ν→ x C.∘ G.₁ x C.▶ g.Γ a ⌝ C.∘ C.α→ _ C.∘ α.ν→ x C.◀ β.σ a C.∘ C.α← _
      ≡⟨ ap! g.is-natural ⟩
        C.α← _ C.∘ f.Γ b C.◀ (β'.σ b C.⊗ F.₁ x)
    C.∘ α.σ b C.▶ (g.Γ b C.◀ F.₁ x C.∘ β.ν→ x) C.∘ C.α→ _ C.∘ α.ν→ x C.◀ β.σ a C.∘ C.α← _
      ≡⟨ bicat! C ⟩
        (f.Γ b C.◆ g.Γ b) C.◀ F.₁ x C.∘ C.α← _ C.∘ α.σ b C.▶ β.ν→ x C.∘ C.α→ _
    C.∘ α.ν→ x C.◀ β.σ a C.∘ C.α← _
      ∎
