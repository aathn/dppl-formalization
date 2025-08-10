module Lib.Cat.Bi where

open import Cat.Prelude

open import Cat.Bi.Base
open import Cat.Functor.Base
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Naturality
open import Cat.Instances.Discrete
open import Cat.Instances.Product
import Cat.Reasoning as Cr
import Cat.Functor.Reasoning as Fr

open Functor
open _=>_

module _ {o h ℓ ℓx ℓp} (BC : Prebicategory o h ℓ) (O : Prebicategory.Ob BC → Type ℓx) where
  module BC = Prebicategory BC
  open Prebicategory

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
        → H A B F → H B C G → H A C (BC.compose.₀ (G , F)))
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
      { F₀   = λ ((F , F-mor) , (G , G-mor)) → BC.compose.₀ (F , G) , H-∘ G F G-mor F-mor
      ; F₁   = BC.compose.₁
      ; F-id = BC.compose.F-id
      ; F-∘  = BC.compose.F-∘
      }

    B-assoc : Associator-for B[_,_] B-compose
    B-assoc = to-natural-iso record
      { eta = λ _ → BC.associator .to .η _
      ; inv = λ _ → BC.associator .from .η _
      ; eta∘inv = λ ((f , _) , (g , _) , (h , _)) →
          BC.associator .inverses .invl ηₚ (f , g , h)
      ; inv∘eta = λ ((f , _) , (g , _) , (h , _)) →
          BC.associator .inverses .invr ηₚ (f , g , h)
      ; natural = λ _ _ α → sym $ BC.associator .to .is-natural _ _ α
      }

    pb : Prebicategory _ _ _
    pb .Ob = Ob'
    pb .Hom = B[_,_]
    pb .id = B-id
    pb .compose = B-compose
    pb .unitor-r = to-natural-iso record
      { eta = λ _ → BC.unitor-r .to .η _
      ; inv = λ _ → BC.unitor-r .from .η _
      ; eta∘inv = λ (f , _) → BC.unitor-r .inverses .invl ηₚ f
      ; inv∘eta = λ (f , _) → BC.unitor-r .inverses .invr ηₚ f
      ; natural = λ _ _ α → sym $ BC.unitor-r .to .is-natural _ _ α
      }
    pb .unitor-l = to-natural-iso record
      { eta = λ _ → BC.unitor-l .to .η _
      ; inv = λ _ → BC.unitor-l .from .η _
      ; eta∘inv = λ (f , _) → BC.unitor-l .inverses .invl ηₚ f
      ; inv∘eta = λ (f , _) → BC.unitor-l .inverses .invr ηₚ f
      ; natural = λ _ _ α → sym $ BC.unitor-l .to .is-natural _ _ α
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

module Reasoning {o h ℓ} (C : Prebicategory o h ℓ) where
  open Prebicategory C public

  private
    module CH {a} {b} = Cr (Hom a b)
    module CC {A} {B} {C} = Fr (compose {A} {B} {C})

    variable
      X Y : Ob
      F G H : X ↦ Y
      α : G ⇒ H
      β : F ⇒ G

  ◀-distribl : ∀ {Z} {h : Z ↦ X} → (α ∘ β) ◀ h ≡ α ◀ h ∘ β ◀ h
  ◀-distribl {α = α} {β = β} =
    ap (CC.₁ ⊙ (α ∘ β ,_)) (sym (CH.idl CH.id)) ∙ CC.F-∘ _ _

  ▶-distribr : ∀ {Z} {h : Y ↦ Z} → h ▶ (α ∘ β) ≡ h ▶ α ∘ h ▶ β
  ▶-distribr {α = α} {β = β} =
    ap (CC.₁ ⊙ (_, α ∘ β)) (sym (CH.idl CH.id)) ∙ CC.F-∘ _ _

unquoteDecl H-Level-Modification = declare-record-hlevel 2 H-Level-Modification (quote Modification)

module _ {o₁ h₁ ℓ₁ o₂ h₂ ℓ₂} {B : Prebicategory o₁ h₁ ℓ₁} {C : Prebicategory o₂ h₂ ℓ₂} where
  private
    module B = Prebicategory B
    module C = Reasoning C
    module CH {a} {b} = Cr (C.Hom a b)
    module CC {A} {B} {C} = Fr (C.compose {A} {B} {C})

  module _ {F G : Lax-functor B C} where
    private
      module F = Lax-functor F
      module G = Lax-functor G

    open Lax-transfor
    open Modification

    idmd : {α : Lax-transfor F G} → Modification α α
    idmd .Γ _ = CH.id
    idmd .is-natural = CC.elimr refl ∙ CC.introl refl

    _∘md_ : {α β γ : Lax-transfor F G} → Modification β γ → Modification α β → Modification α γ
    _∘md_ f g .Γ a = f .Γ a C.∘ g .Γ a
    _∘md_ {x} {y} {z} f g .is-natural {a} {b} {f = h} =
      ν→ z h C.∘ G.₁ h C.▶ (f .Γ a C.∘ g .Γ a)         ≡⟨ CH.refl⟩∘⟨ C.▶-distribr ⟩
      ν→ z h C.∘ G.₁ h C.▶ f .Γ a C.∘ G.₁ h C.▶ g .Γ a ≡⟨ CH.extendl $ f .is-natural ⟩
      f .Γ b C.◀ F.₁ h C.∘ ν→ y h C.∘ G.₁ h C.▶ g .Γ a ≡⟨ CH.refl⟩∘⟨ g .is-natural ⟩
      f .Γ b C.◀ F.₁ h C.∘ g .Γ b C.◀ F.₁ h C.∘ ν→ x h ≡⟨ CH.pulll $ sym C.◀-distribl ⟩
      (f .Γ b C.∘ g .Γ b) C.◀ F.₁ h C.∘ ν→ x h         ∎

    opaque
      Mod-is-set : {α β : Lax-transfor F G} → is-set (Modification α β)
      Mod-is-set = hlevel 2

    Mod-pathp : {α α' β β' : Lax-transfor F G}
              → (p : α ≡ α') (q : β ≡ β')
              → {a : Modification α β} {b : Modification α' β'}
              → (∀ x → PathP _ (a .Γ x) (b .Γ x))
              → PathP (λ i → Modification (p i) (q i)) a b
    Mod-pathp p q path i .Γ x = path x i
    Mod-pathp p q {a} {b} path i .is-natural {x} {y} {f} =
      is-prop→pathp
        (λ i → CH.Hom-set _ _
          (ν→ (q i) f C.∘ G.₁ f C.▶ path x i) (path y i C.◀ F.₁ f C.∘ ν→ (p i) f))
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
        → ⦃ sa : {x : B.Ob} → Extensional (Lax-transfor.σ α x C.⇒ Lax-transfor.σ β x) ℓr ⦄
        → Extensional (Modification α β) _
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
    ; idr = λ _ → ext λ _ → CH.idr _
    ; idl = λ _ → ext λ _ → CH.idl _
    ; assoc = λ _ _ _ → ext λ _ → CH.assoc _ _ _
    }
