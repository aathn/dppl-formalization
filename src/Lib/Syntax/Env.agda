module Lib.Syntax.Env where

open import Lib.Prelude
open import Lib.Data.Finset
open import Lib.Data.Dec
open import Lib.LocallyNameless.Unfinite

open import Cat.Base
open import Cat.Cartesian

open import Data.Dec.Base
open import Data.Finset.Base
open import Data.Finset.Properties
open import Data.List.Base
open import Data.List.Properties
open import Data.Set.Coequaliser

open FinsetSyntax

-- We define raw environments as basic association lists.
RawEnv : ∀ {ℓ} → Type ℓ → Type ℓ
RawEnv X = List (𝔸 × X)

private variable
  ℓ : Level
  X : Type ℓ
  x : 𝔸 × X
  a : 𝔸
  T : X
  l l' : RawEnv X

raw-dom : RawEnv X → Finset 𝔸
raw-dom = map fst ∘ from-list

-- Two environments are related under dup-step precisely if the second
-- is the result of removing a single duplicate key from the first.
data dup-step {X : Type ℓ} : RawEnv X → RawEnv X → Type ℓ where
  step-cong : dup-step l l' → dup-step (x ∷ l) (x ∷ l')
  step-dup  : fst x ∈ raw-dom l → dup-step (x ∷ l) l

-- We form the type of proper environments as the quotient of RawEnv
-- under dup-step.
Env : Type ℓ → Type ℓ
Env X = RawEnv X / dup-step

private variable
  Γ Γ' : Env X

pattern ε         = inc []
pattern [_∶_] x T = inc ((x , T) ∷ [])

env-cons : (𝔸 × X) → Env X → Env X
env-cons x = Coeq-rec (λ Γ → inc (x ∷ Γ)) λ (_ , _ , Hdup) → quot (step-cong Hdup)

infixl 5 _,_∶_
_,_∶_ : Env X → 𝔸 → X → Env X
Γ , a ∶ T = env-cons (a , T) Γ

dup-raw-dom : dup-step l l' → raw-dom l ≡ raw-dom l'
dup-raw-dom (step-cong Hdup) = ap (_ ∷_) (dup-raw-dom Hdup)
dup-raw-dom (step-dup  H∈)   = sym $ uncons _ _ H∈

env-dom : Env X → Finset 𝔸
env-dom = Coeq-rec raw-dom λ (_ , _ , Hdup) → dup-raw-dom Hdup

env-cons-∈ : a ∈ env-dom Γ → (Γ , a ∶ T) ≡ Γ
env-cons-∈ {Γ = Γ} =
  Coeq-elim-prop {C = λ Γ → ∀ {a T} → a ∈ env-dom Γ → (Γ , a ∶ T) ≡ Γ}
    (λ _ → hlevel 1) (λ _ H∈ → quot (step-dup H∈)) Γ

step-++ₗ : {l1 : RawEnv X} → dup-step l l' → dup-step (l1 ++ l) (l1 ++ l')
step-++ₗ {l1 = []}    Hdup = Hdup
step-++ₗ {l1 = _ ∷ _} Hdup = step-cong (step-++ₗ Hdup)

raw-append : RawEnv X → Env X → Env X
raw-append l = Coeq-rec (λ Γ → inc (l ++ Γ)) λ (_ , _ , Hdup) → quot (step-++ₗ Hdup)

raw-dom-++ : (l l' : RawEnv X) → raw-dom (l ++ l') ≡ (raw-dom l ∪ raw-dom l')
raw-dom-++ l l' =
  ap (map fst) (from-list-++ l l') ∙
  map-union (from-list l) (from-list l') fst

step-++ᵣ : {l1 : RawEnv X} → dup-step l l' → dup-step (l ++ l1) (l' ++ l1)
step-++ᵣ (step-cong Hdup) = step-cong (step-++ᵣ Hdup)
step-++ᵣ {l' = l'} {l1} (step-dup H∈) =
  step-dup $ subst (_ ∈ᶠˢ_) (sym $ raw-dom-++ l' l1) (unionl-∈ᶠˢ _ _ _ H∈)

dup-append : (Γ : Env X) → dup-step l l' → raw-append l Γ ≡ raw-append l' Γ
dup-append {l = l} {l'} Γ =
  Coeq-elim-prop {C = λ Γ → dup-step l l' → raw-append l Γ ≡ raw-append l' Γ}
    (λ _ → hlevel 1) (λ l1 Hdup → quot (step-++ᵣ {l1 = l1} Hdup)) Γ

env-append : Env X → Env X → Env X
env-append Γ Γ' =
  Coeq-rec (λ l → raw-append l Γ') (λ (_ , _ , Hdup) → dup-append Γ' Hdup) Γ

infixl 5 _&_
_&_ : Env X → Env X → Env X
Γ & Γ' = env-append Γ' Γ

env-dom-++ : (Γ Γ' : Env X) → env-dom (Γ' & Γ) ≡ (env-dom Γ ∪ env-dom Γ')
env-dom-++ =
  Coeq-elim-prop (λ _ → hlevel 1) λ l  →
  Coeq-elim-prop (λ _ → hlevel 1) λ l' →
  raw-dom-++ l l'

data raw-mem {X : Type ℓ} (a : 𝔸) (T : X) : RawEnv X → Type ℓ where
  here  : x ≡ᵢ (a , T) → a ∉ raw-dom l → raw-mem a T (x ∷ l)
  there : raw-mem a T l → raw-mem a T (x ∷ l)

raw-mem-∈ : raw-mem a T l → a ∈ raw-dom l
raw-mem-∈ (here reflᵢ H∉) = hereₛ
raw-mem-∈ (there H∈)      = thereₛ (raw-mem-∈ H∈)

-- ∈-raw-mem : a ∈ raw-dom l → Σ[ T ∈ X ] raw-mem a T l
-- ∈-raw-mem H∈ = {!!}

raw-mem-is-prop : ⦃ _ : H-Level X 2 ⦄ {T : X} → is-prop (raw-mem a T l)
raw-mem-is-prop (here reflᵢ H∉) (here _ H∉')  = ap₂ here prop! (is-yes-is-prop H∉ H∉')
raw-mem-is-prop (here reflᵢ H∉) (there Hmem') = absurd (is-no-false H∉ (raw-mem-∈ Hmem'))
raw-mem-is-prop (there Hmem) (here _ H∉')     = absurd (is-no-false H∉' (raw-mem-∈ Hmem))
raw-mem-is-prop (there Hmem) (there Hmem')    = ap there (raw-mem-is-prop Hmem Hmem')

instance
  H-Level-raw-mem : ∀ ⦃ _ : H-Level X 2 ⦄ {T : X} {n} → H-Level (raw-mem a T l) (suc n)
  H-Level-raw-mem = basic-instance 1 raw-mem-is-prop

private
  dup-memr : dup-step l l' → raw-mem a T l → raw-mem a T l'
  dup-memr {a = a} (step-cong Hdup) (here reflᵢ H∉) =
    here reflᵢ (subst (a ∉_) (dup-raw-dom Hdup) H∉)
  dup-memr (step-cong Hdup) (there Hmem) = there (dup-memr Hdup Hmem)
  dup-memr (step-dup H∈) (here reflᵢ H∉) = absurd (is-no-false H∉ H∈)
  dup-memr (step-dup H∈) (there Hmem) = Hmem
  
  dup-meml : dup-step l l' → raw-mem a T l' → raw-mem a T l
  dup-meml {a = a} (step-cong Hdup) (here reflᵢ H∉) =
    here reflᵢ (subst (a ∉_) (sym $ dup-raw-dom Hdup) H∉)
  dup-meml (step-cong Hdup) (there Hmem) = there (dup-meml Hdup Hmem)
  dup-meml (step-dup _) Hmem = there Hmem

env-mem : {X : Type ℓ} → ⦃ H-Level X 2 ⦄ → 𝔸 → X → Env X → Prop ℓ
env-mem a T = Coeq-rec (λ l → el! (raw-mem a T l)) λ (_ , _ , Hdup) →
  n-ua (prop-ext! (dup-memr Hdup) (dup-meml Hdup))

instance
  Membership-Env : {X : Type ℓ} → ⦃ H-Level X 2 ⦄ → Membership (𝔸 × X) (Env X) ℓ
  Membership-Env = record { _∈_ = λ (x , T) Γ → ⌞ env-mem x T Γ ⌟ }

infixl 5 _∶_∈_
_∶_∈_ : {X : Type ℓ} → ⦃ H-Level X 2 ⦄ → 𝔸 → X → Env X → Type ℓ
a ∶ T ∈ Γ = ⌞ env-mem a T Γ ⌟

raw-nub : RawEnv X → RawEnv X
raw-nub []      = []
raw-nub (x ∷ l) =
  ifᵈ holds? (fst x ∈ raw-dom (raw-nub l)) then
    raw-nub l
  else
    x ∷ raw-nub l

raw-dom-nub : (l : RawEnv X) → raw-dom (raw-nub l) ≡ raw-dom l
raw-dom-nub [] = refl
raw-dom-nub (x ∷ l) with holds? (fst x ∈ raw-dom (raw-nub l))
... | yes H∈ = uncons _ _ H∈ ∙ ap (fst x ∷_) (raw-dom-nub l)
... | no  H∉ = ap (fst x ∷_) (raw-dom-nub l)

dup-raw-nub : dup-step l l' → raw-nub l ≡ raw-nub l'
dup-raw-nub (step-cong {x = x} Hdup) =
  ap (λ l → ifᵈ (holds? (fst x ∈ raw-dom l)) then l else x ∷ l) (dup-raw-nub Hdup)
dup-raw-nub (step-dup  {x = x} {l} H∈) =
  ifᵈ-yes (holds? (fst x ∈ raw-dom (raw-nub l)))
    (true-is-yes (subst (fst x ∈_) (sym $ raw-dom-nub l) H∈))

env-nub : ⦃ H-Level X 2 ⦄ → Env X → RawEnv X
env-nub = Coeq-rec raw-nub λ (_ , _ , Hdup) → dup-raw-nub Hdup

inc-raw-nub : (l : RawEnv X) → Path (Env X) (inc l) (inc (raw-nub l))
inc-raw-nub [] = refl
inc-raw-nub (x ∷ l) with holds? (fst x ∈ raw-dom (raw-nub l))
... | yes H∈ = env-cons-∈ (subst (fst x ∈_) (raw-dom-nub l) H∈) ∙ inc-raw-nub l
... | no  _  = ap (env-cons x) (inc-raw-nub l)

env-nub-univ : ⦃ _ : H-Level X 2 ⦄ (Γ : Env X) → Γ ≡ inc (env-nub Γ)
env-nub-univ = Coeq-elim-prop (λ _ → hlevel 1) inc-raw-nub

raw-nub-cons
  : (l : RawEnv X) → a ∉ raw-dom l
  → raw-nub ((a , T) ∷ l) ≡ (a , T) ∷ raw-nub l
raw-nub-cons {a = a} l H∉ = ifᵈ-no (holds? (a ∈ raw-dom (raw-nub l)))
  (subst (a ∉_) (sym $ raw-dom-nub l) H∉)

env-nub-cons
  : ⦃ _ : H-Level X 2 ⦄ (Γ : Env X)
  → a ∉ env-dom Γ → env-nub (Γ , a ∶ T) ≡ (a , T) ∷ env-nub Γ
env-nub-cons = Coeq-elim-prop (λ _ → hlevel 1) raw-nub-cons

module EnvDenot
  {o ℓ} {C : Precategory o ℓ} (cart : Cartesian-category C)
  (X-denot : X → Precategory.Ob C) where
  module C = Cartesian-category cart
  open C

  RawEnv-denot : RawEnv X → Ob
  RawEnv-denot []            = top
  RawEnv-denot ((_ , T) ∷ l) = RawEnv-denot l ⊗₀ X-denot T

  instance
    ⟦⟧-RawEnv : ⟦⟧-notation (RawEnv X)
    ⟦⟧-RawEnv = brackets _ RawEnv-denot

  instance
    ⟦⟧-Env : ⦃ H-Level X 2 ⦄ → ⟦⟧-notation (Env X)
    ⟦⟧-Env = brackets _ λ Γ → ⟦ env-nub Γ ⟧

  raw-lookup : raw-mem a T l → Hom ⟦ l ⟧ (X-denot T)
  raw-lookup {l = _ ∷ l} (here reflᵢ H∉) = π₂
  raw-lookup {l = x ∷ _} (there H∈)      = raw-lookup H∈ C.∘ π₁

  env-lookup : ⦃ _ : H-Level X 2 ⦄ → a ∶ T ∈ Γ → Hom ⟦ Γ ⟧ (X-denot T)
  env-lookup {a = a} {T} {Γ} H∈ = raw-lookup (subst (a ∶ T ∈_) (env-nub-univ Γ) H∈)

-- dom-∈ : {Γ : Env X} {x : 𝔸} → x ∈ dom Γ → Σ[ T ∈ X ] (x , T) ∈ Γ
-- dom-∈ = {!!}
-- dom-∈ {Γ = x ∷ Γ} (∈∪₁ ∈[]) = _ , here refl
-- dom-∈ {Γ = x ∷ Γ} (∈∪₂ x∈Γ) with T , H∈ ← dom-∈ x∈Γ = T , there H∈

-- ∈-dom : {x : 𝔸} → (x , T) ∈ˡ Γ → x ∈ dom Γ
-- ∈-dom {Γ = x ∷ Γ} (here refl) = ∈∪₁ ∈[]
-- ∈-dom {Γ = x ∷ Γ} (there H∈)  = ∈∪₂ (∈-dom H∈)

-- ∉-dom-⊆ :
--   {Δ Γ : Env X}
--   {x : 𝔸}
--   (_ : Δ ⊆ Γ)
--   → -------------------
--   x ∉ dom Γ → x ∉ dom Δ
-- ∉-dom-⊆ {Δ = []} H⊆ H∉ = ∉Ø
-- ∉-dom-⊆ {Δ = _ ∷ Δ} (_ ∷ʳ H⊆) ∉∪ = ∉-dom-⊆ H⊆ it
-- ∉-dom-⊆ {Δ = y ∷ Δ} (refl ∷ H⊆) (∉∪ {{p}}) = ∉∪ {{p = p}} {{∉-dom-⊆ H⊆ it}}

-- ⊆-strengthen :
--   {Γ₂ Γ₁ Γ : Env X}
--   {x : 𝔸}
--   (_ : x ∉ dom Γ)
--   (_ : Γ ⊆ Γ₁ , x ∶ T & Γ₂)
--   → -----------------------
--   Γ ⊆ Γ₁ & Γ₂
-- ⊆-strengthen {Γ₂ = []} H∉ (.(_ , _) ∷ʳ H⊆) = H⊆
-- ⊆-strengthen {Γ₂ = []} {x = x} (∉∪ {{∉[]}}) (refl ∷ H⊆) with () ← ¬≠ x it
-- ⊆-strengthen {Γ₂ = x ∷ Γ₂} H∉ (.x ∷ʳ H⊆) = x ∷ʳ (⊆-strengthen H∉ H⊆)
-- ⊆-strengthen {Γ₂ = x ∷ Γ₂} ∉∪ (x₁ ∷ H⊆) = x₁ ∷ (⊆-strengthen it H⊆)

-- ⊆-split :
--   {Γ₂ Γ₁ Δ : Env X}
--   {x : 𝔸}
--   (_ : x ∉ dom Γ₁ ∪ dom Γ₂)
--   (_ : x ∈ dom Δ)
--   (_ : Δ ⊆ Γ₁ , x ∶ T & Γ₂)
--   → -------------------------------------------------------
--   ∃ λ Δ₁ → ∃ λ Δ₂ → Δ₁ ⊆ Γ₁ × Δ₂ ⊆ Γ₂ × Δ ≡ Δ₁ , x ∶ T & Δ₂

-- ⊆-split {Γ₂ = []} ∉∪ H∈ (.(_ , _) ∷ʳ Hsub) with _ , H∈′ ← dom-∈ H∈
--   with () ← ∉→¬∈ (∈-dom $ lookup Hsub H∈′)
-- ⊆-split {Γ₂ = []} ∉∪ H∈ (refl ∷ Hsub) = _ , _ , Hsub , [] , refl
-- ⊆-split {Γ₂ = x ∷ Γ₂} (∉∪ {{q = ∉∪}}) H∈ (.x ∷ʳ Hsub)
--   with  Δ₁ , Δ₂ , Hsub1 , Hsub2 , Heq ← ⊆-split ∉∪ H∈ Hsub =
--   Δ₁ , Δ₂ , Hsub1 , x ∷ʳ Hsub2 , Heq
-- ⊆-split {Γ₂ = x ∷ Γ₂} (∉∪ {{ q = ∉∪ }}) (∈∪₂ H∈) (refl ∷ Hsub)
--   with Δ₁ , Δ₂ , Hsub1 , Hsub2 , refl ← ⊆-split ∉∪ H∈ Hsub =
--   Δ₁ , x ∷ Δ₂ , Hsub1 , refl ∷ Hsub2 , refl
-- ⊆-split {Γ₂ = Γ₂ , x ∶ _} (∉∪ {{ q = ∉∪ {{ p = ∉[] }} }}) (∈∪₁ ∈[]) (refl ∷ Hsub)
--   with () ← ¬≠ x it
