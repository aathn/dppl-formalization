module Lib.Cat.Bi.Lax-functor where

open import Lib.Cat.Product
import Lib.Cat.Bi.Reasoning as Br
import Lib.Cat.Bi.Solver as Solver

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Functor.Base
open import Cat.Functor.Coherence hiding (_◆_)
open import Cat.Instances.Product
import Cat.Reasoning as Cr

open _=>_
open Functor

-- module _ {o₁ h₁ ℓ₁ o₂ h₂ ℓ₂ o₃ ℓ₃ h₃}
--   {B : Prebicategory o₁ h₁ ℓ₁}
--   {C : Prebicategory o₂ h₂ ℓ₂}
--   {D : Prebicategory o₃ h₃ ℓ₃} where
--   private
--     module B = Prebicategory B
--     module C = Reasoning C
--     module D = Reasoning D
--     module CH = C.Hom
--     module DH = D.Hom

--   _L∘_ : Lax-functor C D → Lax-functor B C → Lax-functor B D
--   F L∘ G = lf where
--     open Lax-functor
--     open Cr._≅_
--     module F = Lax-functor F
--     module G = Lax-functor G
--     -- These proofs are horrible...
--     lf : Lax-functor _ _
--     lf .P₀ = F.P₀ ⊙ G.P₀
--     lf .P₁ = F.P₁ F∘ G.P₁
--     lf .compositor =
--       (nat-assoc-to ⊙ nat-assoc-from) (F.P₁ ▸ G.compositor)
--       ∘nt nat-unassoc-from (F.compositor ◂ (G.P₁ F× G.P₁))
--       ∘nt (D.compose ▸ F×-interchange _ _ _ _ .to)
--     lf .unitor = F.₂ G.unitor D.∘ F.unitor
--     lf .hexagon f g h = {!!}
--       --   F.₂ (G.₂ (B.α→ f g h)) D.∘
--       --   (F.₂ (G.γ→ (f B.⊗ g) h) D.∘ F.γ→ (G.₁ (f B.⊗ g)) (G.₁ h) D.∘ (DH.id D.◆ DH.id)) D.∘
--       --   (F.₂ (G.γ→ f g) D.∘ F.γ→ (G.₁ f) (G.₁ g) D.∘ (DH.id D.◆ DH.id)) D.◀ F.₁ (G.₁ h)
--       -- ≡⟨ {!!} ⟩
--       --   (F.₂ (G.γ→ f (g B.⊗ h)) D.∘ F.γ→ (G.₁ f) (G.₁ (g B.⊗ h)) D.∘ (DH.id D.◆ DH.id)) D.∘
--       --   (F.₁ (G.₁ f) D.▶ (F.₂ (G.γ→ g h) D.∘ F.γ→ (G.₁ g) (G.₁ h) D.∘ (DH.id D.◆ DH.id))) D.∘
--       --   D.α→ (F.₁ (G.₁ f)) (F.₁ (G.₁ g)) (F.₁ (G.₁ h))
--       -- ∎
--     lf .right-unit f = {!!}
--       --   F.₂ (G.₂ (B.ρ← f)) D.∘
--       --   (F.₂ (G.γ→ f B.id) D.∘ ⌜ F.γ→ (G.₁ f) (G.₁ B.id) D.∘ (DH.id D.◆ DH.id) ⌝) D.∘
--       --   (F.₁ (G.₁ f) D.▶ (F.₂ G.unitor D.∘ F.unitor))
--       -- ≡⟨ DH.pulll (F.P₁.pulll refl) ∙ ap! (DH.elimr D.⊗.F-id) ⟩
--       --   (F.₂ (G.₂ (B.ρ← f) CH.∘ G.γ→ f B.id) D.∘ F.γ→ (G.₁ f) (G.₁ B.id)) D.∘
--       --   ⌜ F.₁ (G.₁ f) D.▶ (F.₂ G.unitor D.∘ F.unitor) ⌝
--       -- ≡⟨ ap! D.▶-distribr ⟩
--       --   (F.₂ (G.₂ (B.ρ← f) CH.∘ G.γ→ f B.id) D.∘ F.γ→ (G.₁ f) (G.₁ B.id)) D.∘
--       --   (⌜ DH.id ⌝ D.◆ F.₂ G.unitor) D.∘ F.₁ (G.₁ f) D.▶ F.unitor
--       -- ≡⟨ ap! (sym F.P₁.F-id) ∙ DH.pulll (sym $ DH.assoc _ _ _) ⟩
--       --   (F.₂ (G.₂ (B.ρ← f) CH.∘ G.γ→ f B.id) D.∘
--       --   ⌜ F.γ→ (G.₁ f) (G.₁ B.id) D.∘ (F.₂ CH.id D.◆ F.₂ G.unitor) ⌝) D.∘
--       --   (F.₁ (G.₁ f) D.▶ F.unitor)
--       -- ≡⟨ ap! (F.compositor .is-natural _ _ (CH.id , G.unitor)) ⟩
--       --   (F.₂ (G.₂ (B.ρ← f) CH.∘ G.γ→ f B.id) D.∘
--       --   (F.₂ (G.₁ f C.▶ G.unitor) D.∘ F.γ→ _ _)) D.∘
--       --   (F.₁ (G.₁ f) D.▶ F.unitor)
--       -- ≡⟨ F.P₁.pulll (sym $ CH.assoc _ _ _) DH.⟩∘⟨refl ⟩
--       --   (⌜ F.₂ (G.₂ (B.ρ← f) CH.∘ G.γ→ f B.id CH.∘ (G.₁ f C.▶ G.unitor)) ⌝ D.∘
--       --   F.γ→ _ _) D.∘ (F.₁ (G.₁ f) D.▶ F.unitor)
--       -- ≡⟨ ap! (F.P₁.⟨ G.right-unit f ⟩) ⟩
--       --   (F.₂ (C.ρ← (G.₁ f)) D.∘ F.γ→ _ _) D.∘ (F.₁ (G.₁ f) D.▶ F.unitor)
--       -- ≡⟨ sym (DH.assoc _ _ _) ∙ F.right-unit (G.P₁.₀ f) ⟩
--       --   D.ρ← (F.₁ (G.₁ f))
--       -- ∎
--     lf .left-unit f = {!!}
--       --   F.₂ (G.₂ (B.λ← f)) D.∘
--       --   (F.₂ (G.γ→ B.id f) D.∘ ⌜ F.γ→ (G.₁ B.id) (G.₁ f) D.∘ (DH.id D.◆ DH.id) ⌝) D.∘
--       --   (F.₂ G.unitor D.∘ F.unitor) D.◀ F.₁ (G.₁ f)
--       -- ≡⟨ DH.pulll (F.P₁.pulll refl) ∙ ap! (DH.elimr D.⊗.F-id) ⟩
--       --   (F.₂ (G.₂ (B.λ← f) C.∘ G.γ→ B.id f) D.∘ F.γ→ (G.₁ B.id) (G.₁ f)) D.∘
--       --   ⌜ (F.₂ G.unitor D.∘ F.unitor) D.◀ F.₁ (G.₁ f) ⌝
--       -- ≡⟨ ap! D.◀-distribl ⟩
--       --   (F.₂ (G.₂ (B.λ← f) C.∘ G.γ→ B.id f) D.∘ F.γ→ (G.₁ B.id) (G.₁ f)) D.∘
--       --   (F.₂ G.unitor D.◆ ⌜ DH.id ⌝) D.∘ F.unitor D.◀ F.₁ (G.₁ f)
--       -- ≡⟨ ap! (sym F.P₁.F-id) ∙ DH.pulll (sym $ DH.assoc _ _ _) ⟩
--       --   (F.₂ (G.₂ (B.λ← f) C.∘ G.γ→ B.id f) D.∘
--       --   ⌜ F.γ→ (G.₁ B.id) (G.₁ f) D.∘ (F.₂ G.unitor D.◆ F.₂ CH.id) ⌝) D.∘
--       --   F.unitor D.◀ F.₁ (G.₁ f)
--       -- ≡⟨ ap! (F.compositor .is-natural _ _ (G.unitor , CH.id)) ⟩
--       --   (F.₂ (G.₂ (B.λ← f) C.∘ G.γ→ B.id f) D.∘
--       --   (F.₂ (G.unitor C.◀ G.₁ f) D.∘ F.γ→ _ _)) D.∘
--       --   F.unitor D.◀ F.₁ (G.₁ f)
--       -- ≡⟨ F.P₁.pulll (sym $ CH.assoc _ _ _) DH.⟩∘⟨refl ⟩
--       --   (⌜ F.₂ (G.₂ (B.λ← f) C.∘ G.γ→ B.id f C.∘ G.unitor C.◀ G.₁ f) ⌝ D.∘
--       --   F.γ→ _ _) D.∘ F.unitor D.◀ F.₁ (G.₁ f)
--       -- ≡⟨ ap! (F.P₁.⟨ G.left-unit f ⟩) ⟩
--       --   (F.₂ (C.λ← (G.₁ f)) D.∘ F.γ→ _ _) D.∘ F.unitor D.◀ F.₁ (G.₁ f)
--       -- ≡⟨ sym (DH.assoc _ _ _) ∙ F.left-unit (G.₁ f) ⟩
--       --   D.λ← (F.₁ (G.₁ f))
--       -- ∎


unquoteDecl H-Level-Modification = declare-record-hlevel 2 H-Level-Modification (quote Modification)

module _ {o₁ h₁ ℓ₁ o₂ h₂ ℓ₂} {B : Prebicategory o₁ h₁ ℓ₁} {C : Prebicategory o₂ h₂ ℓ₂} where
  open Br C
  open Hom hiding (Ob ; id ; _∘_)
  open Solver C

  private
    module B = Prebicategory B

  open Lax-transfor
  open Modification
  open Cr._≅_
  open Cr.Inverses

  idlx : {F : Lax-functor B C} → F =>ₗ F
  idlx {F} = lx where
    module F = Lax-functor F
    ν : ∀ {a b} → preaction C (id {F.₀ b}) F∘ F.P₁ => postaction C (id {F.₀ a}) F∘ F.P₁
    ν = (unitor-l .to ∘nt unitor-r .from) ◂ F.P₁

    lx : F =>ₗ F
    lx .σ a = id {F.₀ a}
    lx .naturator = ν
    lx .ν-compositor {a = a} {c = c} f g = solve
      ((`λ→ _ `∘ `ρ← _) `∘ _↑ {g = F.₁ (f B.⊗ g) ↑} (F.γ→ f g) `◀ `id)
      (`id `▶ F.γ→ f g ↑ `∘ `α→ _ (F.₁ f ↑) (F.₁ g ↑) `∘ (`λ→ _ `∘ `ρ← _) `◀ _ `∘ `α← _ _ _ `∘ _ `▶ (`λ→ _ `∘ `ρ← _) `∘ `α→ _ _ _)
      refl
    lx .ν-unitor = solve
      ((`λ→ _ `∘ `ρ← _) `∘ _↑ {g = F.₁ B.id ↑} F.unitor `◀ `id)
      (`id `▶ F.unitor ↑ `∘ `ρ→ _ `∘ `λ← _)
      refl

  -- _∘lx_ : {F G H : Lax-functor B C} → G =>ₗ H → F =>ₗ G → F =>ₗ H
  -- _∘lx_ {F} {G} {H} α β = lx where
  --   module F = Lax-functor F
  --   module G = Lax-functor G
  --   module H = Lax-functor H
  --   module α = Lax-transfor α
  --   module β = Lax-transfor β
  --   ν : ∀ {a b} → preaction C (α.σ b ⊗ β.σ b) F∘ H.P₁ => postaction C (α.σ a ⊗ β.σ a) F∘ F.P₁
  --   ν {a} {b} =
  --     (▶-assoc .from ◂ F.P₁) ∘nt
  --     nat-assoc-to (postaction C (α.σ a) ▸ β.naturator) ∘nt
  --     (nat-unassoc-to ⊙ nat-unassoc-from) (◀-▶-comm .to ◂ G.P₁) ∘nt
  --     nat-assoc-from (preaction C (β.σ b) ▸ α.naturator) ∘nt
  --     (◀-assoc .to ◂ H.P₁)

  --   lx : _ =>ₗ _
  --   lx .σ x = α.σ x ⊗ β.σ x
  --   lx .naturator = ν
  --   lx .ν-compositor f g = {!!}
  --   lx .ν-unitor {a} =
  --     ν .η B.id ∘ H.unitor ◀ σ lx a ≡⟨ {!!} ⟩ -- solve ((`α← _ _ _ `∘ _ `▶ _ `∘ `α→ _ _ _ `∘ _ `∘ `α← _ _ _) `∘ ` H.unitor `◀ ` σ lx a) ? ? ⟩
  --     -- α← _ _ _ ∘ α.σ a ▶ β.ν→ B.id ∘ α→ _ _ _ ∘
  --     -- α.ν→ B.id ◀ β.σ a ∘ ⌜ α← _ _ _ ∘ H.unitor ◀ (α.σ a ⊗ β.σ a) ⌝ ≡⟨ ap! (◀-assoc .to .is-natural _ _ _) ∙ cat! CH ⟩
  --     α← _ _ _ ∘ α.σ a ▶ β.ν→ B.id ∘ α→ _ _ _ ∘
  --     ⌜ α.ν→ B.id ∘ H.unitor ◀ α.σ a ⌝ ◀ β.σ a ∘ α← _ _ _ ≡⟨ ap! (α.ν-unitor) ⟩
  --     _                                                             ≡⟨ {!!} ⟩
  --     α← _ _ _ ∘ α.σ a ▶ β.ν→ B.id ∘ ⌜ α→ _ _ _ ∘ (α.σ a ▶ G.unitor) ◀ β.σ a ⌝ ∘
  --     ρ→ _ ◀ β.σ a ∘ λ← _ ◀ β.σ a ∘ α← _ _ _                        ≡⟨ ap! (α→nat _ _ _) ⟩
  --     α← _ _ _ ∘ α.σ a ▶ β.ν→ B.id ∘ (α.σ a ▶ (G.unitor ◀ β.σ a) ∘ α→ _ _ _ ) ∘
  --     ρ→ _ ◀ β.σ a ∘ λ← _ ◀ β.σ a ∘ α← _ _ _                        ≡⟨ {!!} ⟩
  --     α← _ _ _ ∘ α.σ a ▶ ⌜ β.ν→ B.id ∘ G.unitor ◀ β.σ a ⌝ ∘ α→ _ _ _ ∘
  --     ρ→ _ ◀ β.σ a ∘ λ← _ ◀ β.σ a ∘ α← _ _ _                                      ≡⟨ ap! β.ν-unitor ⟩
  --     α← _ _ _ ∘ α.σ a ▶ (β.σ a ▶ F.unitor ∘ ρ→ _ ∘ λ← _) ∘ α→ _ _ _ ∘
  --     ρ→ _ ◀ β.σ a ∘ λ← _ ◀ β.σ a ∘ α← _ _ _                                      ≡⟨ {!!} ⟩
  --     ⌜ α← _ _ _ ∘ α.σ a ▶ (β.σ a ▶ F.unitor) ⌝ ∘ α.σ a ▶ ρ→ _ ∘ α.σ a ▶ λ← _ ∘ α→ _ _ _ ∘
  --     ρ→ _ ◀ β.σ a ∘ λ← _ ◀ β.σ a ∘ α← _ _ _                                      ≡⟨ ap! (▶-assoc .from .is-natural _ _ _) ⟩
  --     ((α.σ a ⊗ β.σ a) ▶ F.unitor ∘ α← _ _ _) ∘ α.σ a ▶ ρ→ _ ∘ α.σ a ▶ λ← _ ∘ α→ _ _ _ ∘
  --     ρ→ _ ◀ β.σ a ∘ λ← _ ◀ β.σ a ∘ α← _ _ _                                      ≡⟨ {!!} ⟩
  --     (α.σ a ⊗ β.σ a) ▶ F.unitor ∘ ρ→ (α.σ a ⊗ β.σ a) ∘ λ← (α.σ a ⊗ β.σ a) ∎
  --     where CH = Hom C (F.₀ a) (H.₀ a)

  module _ {F G : Lax-functor B C} where
    private
      module F = Lax-functor F
      module G = Lax-functor G

    idmd : {α : F =>ₗ G} → Modification α α
    idmd .Γ _ = Hom.id
    idmd .is-natural = ⊗.elimr refl ∙ ⊗.introl refl

    _∘md_ : {α β γ : F =>ₗ G} → Modification β γ → Modification α β → Modification α γ
    _∘md_ f g .Γ a = f .Γ a ∘ g .Γ a
    _∘md_ {x} {y} {z} f g .is-natural {a} {b} {f = h} =
      ν→ z h ∘ G.₁ h ▶ (f .Γ a ∘ g .Γ a)       ≡⟨ refl⟩∘⟨ ▶-distribr ⟩
      ν→ z h ∘ G.₁ h ▶ f .Γ a ∘ G.₁ h ▶ g .Γ a ≡⟨ extendl $ f .is-natural ⟩
      f .Γ b ◀ F.₁ h ∘ ν→ y h ∘ G.₁ h ▶ g .Γ a ≡⟨ refl⟩∘⟨ g .is-natural ⟩
      f .Γ b ◀ F.₁ h ∘ g .Γ b ◀ F.₁ h ∘ ν→ x h ≡⟨ pulll $ sym ◀-distribl ⟩
      (f .Γ b ∘ g .Γ b) ◀ F.₁ h ∘ ν→ x h       ∎

    opaque
      Mod-is-set : {α β : Lax-transfor F G} → is-set (Modification α β)
      Mod-is-set = hlevel 2

    Mod-pathp : {α α' β β' : Lax-transfor F G}
              → (p : α ≡ α') (q : β ≡ β')
              → {a : Modification α β} {b : Modification α' β'}
              → (∀ x → PathP _ (a .Γ x) (b .Γ x))
              → PathP (λ i → Modification (p i) (q i)) a b
    Mod-pathp p q path i .Γ x                            = path x i
    Mod-pathp p q {a} {b} path i .is-natural {x} {y} {f} =
      is-prop→pathp
        (λ i → Hom-set _ _
          (ν→ (q i) f ∘ G.₁ f ▶ path x i) (path y i ◀ F.₁ f ∘ ν→ (p i) f))
        (a .is-natural)
        (b .is-natural) i

    Mod-path : {α β : Lax-transfor F G} {a b : Modification α β}
             → ((x : _) → a .Γ x ≡ b .Γ x)
             → a ≡ b
    Mod-path = Mod-pathp refl refl

    _Γᵈ_ : {α α' β β' : Lax-transfor F G} {p : α ≡ α'} {q : β ≡ β'}
         → {a : Modification α β} {b : Modification α' β'}
         → PathP (λ i → Modification (p i) (q i)) a b
         → ∀ x → PathP _ (a .Γ x) (b .Γ x)
    p Γᵈ x = apd (λ i e → e .Γ x) p

    _Γₚ_ : {α β : Lax-transfor F G} {a b : Modification α β} → a ≡ b → ∀ x → a .Γ x ≡ b .Γ x
    p Γₚ x = ap (λ e → e .Γ x) p

    infixl 45 _Γₚ_

    instance
      Extensional-modification
        : ∀ {ℓr} {α β : Lax-transfor F G}
        → ⦃ sa : {x : B.Ob} → Extensional (Lax-transfor.σ α x ⇒ Lax-transfor.σ β x) ℓr ⦄
        → Extensional (Modification α β) (o₁ ⊔ ℓr)
      Extensional-modification ⦃ sa ⦄ .Pathᵉ f g = ∀ i → Pathᵉ sa (f .Γ i) (g .Γ i)
      Extensional-modification ⦃ sa ⦄ .reflᵉ x i = reflᵉ sa (x .Γ i)
      Extensional-modification ⦃ sa ⦄ .idsᵉ .to-path x = Mod-path λ i →
        sa .idsᵉ .to-path (x i)
      Extensional-modification ⦃ sa ⦄ .idsᵉ .to-path-over h =
        is-prop→pathp (λ i → Π-is-hlevel 1 λ _ → Pathᵉ-is-hlevel 1 sa (hlevel 2)) _ _


  Lax[_,_] : Lax-functor B C → Lax-functor B C → Precategory _ _
  Lax[ F , G ] = record
    { Ob = F =>ₗ G
    ; Hom = Modification
    ; Hom-set = λ _ _ → Mod-is-set
    ; id = idmd
    ; _∘_ = _∘md_
    ; idr = λ _ → ext λ _ → idr _
    ; idl = λ _ → ext λ _ → idl _
    ; assoc = λ _ _ _ → ext λ _ → assoc _ _ _
    }

  -- Lax-compose : ∀ {F G H : Lax-functor B C} → Functor (Lax[ G , H ] ×ᶜ Lax[ F , G ]) Lax[ F , H ]
  -- Lax-compose = {!!}
  -- Lax-compose .F₀ (α , β) = α ∘lx β
  -- Lax-compose .F₁ (f , g) = {!!}
  -- Lax-compose .F-id = {!!}
  -- Lax-compose .F-∘ = {!!}
