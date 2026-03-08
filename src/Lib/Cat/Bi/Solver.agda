module Lib.Cat.Bi.Solver where

import Lib.Cat.Bi.Reasoning as Br

open import 1Lab.Reflection
open import 1Lab.Reflection.Solver

open import Cat.Prelude
open import Cat.Bi.Base
import Cat.Morphism as Cm

module NbE {o ℓ ℓ'} (C : Prebicategory o ℓ ℓ') where

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


module Reflection where

  pattern category-args C xs      = _ hm∷ _ hm∷ C v∷ xs
  pattern bicategory-args C xs    = _ hm∷ _ hm∷ _ hm∷ C v∷ xs
  pattern functor-args functor xs =
    _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ functor v∷ xs
  pattern iso-args f xs = _ hm∷ _ hm∷ _ h∷ _ h∷ _ h∷ f v∷ xs
  pattern nt-args nt xs = _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ h∷ _ h∷ nt v∷ xs

  pattern “F₀” functor x =
    def (quote Functor.F₀) (functor-args functor (x v∷ []))

  pattern “F₁” functor f =
    def (quote Functor.F₁) (functor-args functor (_ h∷ _ h∷ f v∷ []))

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

  pattern “∘” α β =
    def (quote Precategory._∘_) (category-args “Hom” (_ h∷ _ h∷ _ h∷ α v∷ β v∷ []))

  pattern “◆” α β = “F₁” “compose” (“,” α β)

  pattern “λ→” f     = “η” (“to” “unitor-l”) f
  pattern “λ←” f     = “η” (“from” “unitor-l”) f
  pattern “ρ→” f     = “η” (“to” “unitor-r”) f
  pattern “ρ←” f     = “η” (“from” “unitor-r”) f
  pattern “α→” f g h = “η” (“to” “associator”) (“,” f (“,” g h))
  pattern “α←” f g h = “η” (“from” “associator”) (“,” f (“,” g h))

  pattern “⇒” f g =
    def (quote Precategory.Hom) (category-args “Hom” (f v∷ g v∷ []))

  mk-bicategory-args : Term → List (Arg Term) → List (Arg Term)
  mk-bicategory-args cat xs = infer-hidden 3 $ cat v∷ xs

  “solve” : Term → Term → Term → Term
  “solve” cat lhs rhs =
    def (quote NbE.solve)
      (mk-bicategory-args cat $ infer-hidden 4 $ lhs v∷ rhs v∷ def (quote refl) [] v∷ [])

  “nf₂” : Term → Term → Term
  “nf₂” cat f = def (quote NbE.nf₂) (mk-bicategory-args cat $ infer-hidden 4 $ f v∷ [])

  build-expr₁ : Term → Term
  build-expr₁ “id₁”     = con (quote NbE.Expr₁.`id) []
  build-expr₁ (“⊗” f g) = con (quote NbE.Expr₁._`⊗_) (build-expr₁ f v∷ build-expr₁ g v∷ [])
  build-expr₁ f         = con (quote NbE.Expr₁._↑) (f v∷ [])

  build-expr₂ : Term → Term → TC Term
  build-expr₂ cat (“id₂” f) = do
    let ef = build-expr₁ f
    pure $ con (quote NbE.Expr₂.`id) (infer-hidden 3 $ cat h∷ infer-hidden 2 (ef h∷ []))
  build-expr₂ cat (“∘” α β) = do
    eα ← build-expr₂ cat α
    eβ ← build-expr₂ cat β
    pure $ con (quote NbE.Expr₂._`∘_) (eα v∷ eβ v∷ [])
  build-expr₂ cat (“◆” α β) = do
    eα ← build-expr₂ cat α
    eβ ← build-expr₂ cat β
    pure $ con (quote NbE.Expr₂._`◆_) (eα v∷ eβ v∷ [])
  build-expr₂ cat (“λ→” f) = do
    let ef = build-expr₁ f
    pure $ con (quote NbE.Expr₂.`λ→) (ef v∷ [])
  build-expr₂ cat (“λ←” f) = do
    let ef = build-expr₁ f
    pure $ con (quote NbE.Expr₂.`λ←) (ef v∷ [])
  build-expr₂ cat (“ρ→” f) = do
    let ef = build-expr₁ f
    pure $ con (quote NbE.Expr₂.`ρ→) (ef v∷ [])
  build-expr₂ cat (“ρ←” f) = do
    let ef = build-expr₁ f
    pure $ con (quote NbE.Expr₂.`ρ←) (ef v∷ [])
  build-expr₂ cat (“α→” f g h) = do
    let
      ef = build-expr₁ f
      eg = build-expr₁ g
      eh = build-expr₁ h
    pure $ con (quote NbE.Expr₂.`α→) (ef v∷ eg v∷ eh v∷ [])
  build-expr₂ cat (“α←” f g h) = do
    let
      ef = build-expr₁ f
      eg = build-expr₁ g
      eh = build-expr₁ h
    pure $ con (quote NbE.Expr₂.`α←) (ef v∷ eg v∷ eh v∷ [])
  build-expr₂ cat f = do
    “⇒” lhs rhs ← infer-type f >>= normalise
      where ty → typeError [ "Expected 2-cell, found " , termErr ty ]
    let
      elhs = build-expr₁ lhs
      erhs = build-expr₁ rhs  
    pure $ con (quote NbE.Expr₂._↑) (infer-hidden 3 $ cat h∷ infer-hidden 2 (elhs h∷ erhs h∷ f v∷ []))

  dont-reduce : List Name
  dont-reduce =
    [ quote Precategory.id
    , quote Precategory._∘_
    , quote Prebicategory.id
    , quote Prebicategory.compose
    , quote Prebicategory.unitor-l
    , quote Prebicategory.unitor-r
    , quote Prebicategory.associator
    , quote Prebicategory.Hom
    , quote Cm._≅_.to
    , quote Cm._≅_.from
    , quote _=>_.η
    , quote Functor.F₀
    , quote Functor.F₁
    ]

  bicat-solver : Term → SimpleSolver
  bicat-solver cat .SimpleSolver.dont-reduce       = dont-reduce
  bicat-solver cat .SimpleSolver.build-expr        = build-expr₂ cat
  bicat-solver cat .SimpleSolver.invoke-solver     = “solve” cat
  bicat-solver cat .SimpleSolver.invoke-normaliser = “nf₂” cat

module _ {o ℓ ℓ'} (C : Prebicategory o ℓ ℓ') where
  macro
    bicat! : Term → TC ⊤
    bicat! hole = do
      `C ← quoteTC C
      mk-simple-solver (Reflection.bicat-solver `C) hole

    bicat-simp! : Term → Term → TC ⊤
    bicat-simp! tm hole = do
      `C ← quoteTC C
      mk-simple-normalise (Reflection.bicat-solver `C) tm hole

    bicat-repr! : Term → Term → TC ⊤
    bicat-repr! tm _ = do
      `C ← quoteTC C
      mk-simple-repr (Reflection.bicat-solver `C) tm

private module _ {o ℓ ℓ'} {C : Prebicategory o ℓ ℓ'} where
  open Br C
  variable
    A B : Ob
    f g h i : A ↦ B
    α β : f ⇒ g

  test-distrib-◁ : f ▶ (α ∘ β) ≡ f ▶ α ∘ f ▶ β
  test-distrib-◁ = bicat! C
  
  test-distrib-▷ : (α ∘ β) ◀ f ≡ α ◀ f ∘ β ◀ f
  test-distrib-▷ = bicat! C

  test-pentagon-α→
    : (f ▶ α→ g h i) ∘ α→ f (g ⊗ h) i ∘ (α→ f g h ◀ i)
    ≡ α→ f g (h ⊗ i) ∘ α→ (f ⊗ g) h i
  test-pentagon-α→ = bicat! C

  test-triangle-ρ← : ρ← (f ⊗ g) ∘ α← f g id ≡ f ▶ ρ← g
  test-triangle-ρ← = bicat! C

  test-triangle-λ← : λ← (f ⊗ g) ∘ α→ id f g ≡ λ← f ◀ g
  test-triangle-λ← = bicat! C
