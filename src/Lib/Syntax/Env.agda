module Lib.Syntax.Env where

open import Lib.Prelude hiding (⟨_,_⟩)
open import Lib.Data.Dec
open import Lib.Data.Finset
open import Lib.Data.List
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
  X Y : Type ℓ
  x : 𝔸 × X
  a : 𝔸
  T : X
  l l' : RawEnv X

raw-dom : RawEnv X → Finset 𝔸
raw-dom = from-list ∘ map fst

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
raw-append l =
  Coeq-rec (λ l' → inc (l ++ l')) λ (_ , _ , Hdup) → quot (step-++ₗ Hdup)

raw-dom-++ : (l l' : RawEnv X) → raw-dom (l ++ l') ≡ (raw-dom l ∪ raw-dom l')
raw-dom-++ l l' =
  ap from-list (map-++ fst l l') ∙ from-list-++ (map fst l) (map fst l')

step-++ᵣ : {l1 : RawEnv X} → dup-step l l' → dup-step (l ++ l1) (l' ++ l1)
step-++ᵣ (step-cong Hdup) = step-cong (step-++ᵣ Hdup)
step-++ᵣ {l' = l'} {l1} (step-dup H∈) =
  step-dup $ subst (_ ∈ᶠˢ_) (sym $ raw-dom-++ l' l1) (unionl-∈ᶠˢ _ _ _ H∈)

dup-append : (Γ : Env X) → dup-step l l' → raw-append l Γ ≡ raw-append l' Γ
dup-append {l = l} {l'} =
  Coeq-elim-prop {C = λ Γ → dup-step l l' → raw-append l Γ ≡ raw-append l' Γ}
    (λ _ → hlevel 1) (λ l1 Hdup → quot (step-++ᵣ {l1 = l1} Hdup))

opaque
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

data is-nubbed {X : Type ℓ} : RawEnv X → Type ℓ where
  []  : is-nubbed []
  _∷_ : fst x ∉ raw-dom l → is-nubbed l → is-nubbed (x ∷ l)

raw-nub-is-nubbed : (l : RawEnv X) → is-nubbed (raw-nub l)
raw-nub-is-nubbed [] = []
raw-nub-is-nubbed (x ∷ l) with holds? (fst x ∈ raw-dom (raw-nub l))
... | yes _ = raw-nub-is-nubbed l
... | no H∉ = false-is-no H∉ ∷ raw-nub-is-nubbed l

env-nub-is-nubbed : ⦃ _ : H-Level X 2 ⦄ (Γ : Env X) → is-nubbed (env-nub Γ)
env-nub-is-nubbed Γ = subst (is-nubbed ∘ env-nub)
  (sym $ env-nub-univ Γ) (raw-nub-is-nubbed (env-nub Γ))

raw-nub-cons
  : (l : RawEnv X) → a ∉ raw-dom l
  → raw-nub ((a , T) ∷ l) ≡ (a , T) ∷ raw-nub l
raw-nub-cons {a = a} l H∉ = ifᵈ-no (holds? (a ∈ raw-dom (raw-nub l)))
  (subst (a ∉_) (sym $ raw-dom-nub l) H∉)

env-nub-cons
  : ⦃ _ : H-Level X 2 ⦄ (Γ : Env X)
  → a ∉ env-dom Γ → env-nub (Γ , a ∶ T) ≡ (a , T) ∷ env-nub Γ
env-nub-cons = Coeq-elim-prop (λ _ → hlevel 1) raw-nub-cons

raw-map : (X → Y) → RawEnv X → RawEnv Y
raw-map f = map (λ (x , T) → x , f T)

step-raw-map : {f : X → Y} → dup-step l l' → dup-step (raw-map f l) (raw-map f l')
step-raw-map (step-cong Hdup) = step-cong (step-raw-map Hdup)
step-raw-map (step-dup {x = x} H∈) = step-dup
  $ subst (fst x ∈_) (ap from-list (sym $ map-comp _ _ _)) H∈

env-map : (X → Y) → Env X → Env Y
env-map f =
  Coeq-rec (λ l → inc (raw-map f l)) λ (_ , _ , Hdup) → quot (step-raw-map Hdup)

data raw-sub {X : Type ℓ} : RawEnv X → RawEnv X → Type ℓ where
  sub-nil : raw-sub [] l
  sub-cons
    : {x y : 𝔸 × X} → x ≡ᵢ y → fst y ∉ raw-dom l'
    → raw-sub l l' → raw-sub (x ∷ l) (y ∷ l')
  sub-consʳ
    : {x y : 𝔸 × X} → fst x ∉ raw-dom l
    → raw-sub (x ∷ l) l' → raw-sub (x ∷ l) (y ∷ l')
  sub-consˡ
    : fst x ∈ raw-dom l
    → raw-sub l l' → raw-sub (x ∷ l) l'

raw-sub→dom-⊆ : raw-sub l l' → raw-dom l ⊆ raw-dom l'
raw-sub→dom-⊆ sub-nil                = λ _ H∈ → absurd (¬mem-[] H∈)
raw-sub→dom-⊆ (sub-cons reflᵢ H∉ H⊆) = λ _ H∈ →
  ∈ᶠˢ-split hereₛ' (λ H∈' → thereₛ (raw-sub→dom-⊆ H⊆ _ H∈')) H∈
raw-sub→dom-⊆ (sub-consʳ H∉ H⊆) = λ _ H∈ → thereₛ (raw-sub→dom-⊆ H⊆ _ H∈)
raw-sub→dom-⊆ (sub-consˡ H∈ H⊆) = λ _ H∈' →
  ∈ᶠˢ-split (λ {reflᵢ → raw-sub→dom-⊆ H⊆ _ H∈}) (raw-sub→dom-⊆ H⊆ _) H∈'

-- ∈-raw-mem : a ∈ raw-dom l → ∃[ T ∈ X ] raw-mem a T l
-- ∈-raw-mem {l = []}    H∈ = absurd (¬mem-[] H∈)
-- ∈-raw-mem {l = x ∷ l} H∈ = ∈ᶠˢ-split
--   (λ { reflᵢ → case holds? (fst x ∈ raw-dom l) of λ where
--        (yes H∈') → case ∈-raw-mem H∈' of λ _ H∈'' → inc (_ , consʳ H∈'')
--        (no  H∉)  → inc (_ , here reflᵢ (false-is-no H∉))
--      })
--   (λ { p → case ∈-raw-mem p of λ _ H∈' → inc (_ , consʳ H∈') })
--   H∈

raw-sub-is-prop : ⦃ _ : H-Level X 2 ⦄ {l l' : RawEnv X} → is-prop (raw-sub l l')
raw-sub-is-prop sub-nil sub-nil                             = refl
raw-sub-is-prop (sub-cons reflᵢ H∉ H⊆) (sub-cons p H∉' H⊆') = λ i →
  sub-cons (q i) (is-yes-is-prop H∉ H∉' i) (raw-sub-is-prop H⊆ H⊆' i) where
  q : reflᵢ ≡ p
  q = prop!
raw-sub-is-prop (sub-cons reflᵢ H∉ H⊆) (sub-consʳ _ H⊆') =
  absurd (is-no-false H∉ (raw-sub→dom-⊆ H⊆' _ hereₛ))
raw-sub-is-prop (sub-cons reflᵢ H∉ H⊆) (sub-consˡ H∈ H⊆') =
  absurd (is-no-false H∉ (raw-sub→dom-⊆ H⊆ _ H∈))
raw-sub-is-prop (sub-consʳ H∉ H⊆) (sub-cons reflᵢ H∉' H⊆') =
  absurd (is-no-false H∉' (raw-sub→dom-⊆ H⊆ _ hereₛ))
raw-sub-is-prop (sub-consʳ H∉ H⊆) (sub-consʳ H∉' H⊆') =
  ap₂ sub-consʳ (is-yes-is-prop H∉ H∉') (raw-sub-is-prop H⊆ H⊆')
raw-sub-is-prop (sub-consʳ H∉ H⊆) (sub-consˡ H∈ H⊆') = absurd (is-no-false H∉ H∈)
raw-sub-is-prop (sub-consˡ H∈ H⊆) (sub-cons reflᵢ H∉ H⊆') =
  absurd (is-no-false H∉ (raw-sub→dom-⊆ H⊆' _ H∈))
raw-sub-is-prop (sub-consˡ H∈ H⊆) (sub-consʳ H∉ H⊆')  = absurd (is-no-false H∉ H∈)
raw-sub-is-prop (sub-consˡ H∈ H⊆) (sub-consˡ H∈' H⊆') =
  ap₂ sub-consˡ prop! (raw-sub-is-prop H⊆ H⊆')

instance
  H-Level-raw-sub
    : ∀ ⦃ _ : H-Level X 2 ⦄ {l l' : RawEnv X} {n} → H-Level (raw-sub l l') (suc n)
  H-Level-raw-sub = basic-instance 1 raw-sub-is-prop

private
  dup-subr
    : ⦃ _ : H-Level X 2 ⦄ {l l1 l2 : RawEnv X}
    → dup-step l1 l2 → raw-sub l l1 ≃ raw-sub l l2
  dup-subr Hdup = prop-ext! (l→r Hdup) (r→l Hdup) where
    l→r : {l l1 l2 : RawEnv X} → dup-step l1 l2 → raw-sub l l1 → raw-sub l l2
    l→r (step-cong Hdup) sub-nil            = sub-nil
    l→r (step-cong Hdup) (sub-cons p H∉ H⊆) =
      sub-cons p (subst (_ ∉_) (dup-raw-dom Hdup) H∉) (l→r Hdup H⊆)
    l→r (step-cong Hdup) (sub-consʳ H∉ H⊆) = sub-consʳ H∉ (l→r Hdup H⊆)
    l→r (step-cong Hdup) (sub-consˡ H∈ H⊆) = sub-consˡ H∈ (l→r (step-cong Hdup) H⊆)
    l→r (step-dup H∈) sub-nil             = sub-nil
    l→r (step-dup H∈) (sub-cons p H∉ H⊆)  = absurd (is-no-false H∉ H∈)
    l→r (step-dup H∈) (sub-consʳ _ H⊆)    = H⊆
    l→r (step-dup H∈) (sub-consˡ H∈' H⊆)  = sub-consˡ H∈' (l→r (step-dup H∈) H⊆)

    r→l : {l l1 l2 : RawEnv X} → dup-step l1 l2 → raw-sub l l2 → raw-sub l l1
    r→l (step-cong Hdup) sub-nil            = sub-nil
    r→l (step-cong Hdup) (sub-cons p H∉ H⊆) =
      sub-cons p (subst (_ ∉_) (sym $ dup-raw-dom Hdup) H∉) (r→l Hdup H⊆)
    r→l (step-cong Hdup) (sub-consʳ H∉ H⊆)   = sub-consʳ H∉ (r→l Hdup H⊆)
    r→l (step-cong Hdup) (sub-consˡ H∈ H⊆)   = sub-consˡ H∈ (r→l (step-cong Hdup) H⊆)
    r→l (step-dup H∈) sub-nil                = sub-nil
    r→l (step-dup H∈) (sub-cons reflᵢ H∉ H⊆) = sub-consʳ
      (false-is-no λ H∈ → is-no-false H∉ (raw-sub→dom-⊆ H⊆ _ H∈))
      (sub-cons reflᵢ H∉ H⊆)
    r→l (step-dup H∈) (sub-consʳ H∉ H⊆)  = sub-consʳ H∉ (sub-consʳ H∉ H⊆)
    r→l (step-dup H∈) (sub-consˡ H∈' H⊆) = sub-consˡ H∈' (r→l (step-dup H∈) H⊆)

  dup-subl
    : ⦃ _ : H-Level X 2 ⦄ {l l1 l2 : RawEnv X}
    → dup-step l1 l2 → raw-sub l1 l ≃ raw-sub l2 l
  dup-subl {X = X} Hdup = prop-ext! (l→r Hdup) (r→l Hdup) where
    l→r : {l l1 l2 : RawEnv X} → dup-step l1 l2 → raw-sub l1 l → raw-sub l2 l
    l→r (step-cong Hdup) (sub-cons p H∉ H⊆) = sub-cons p H∉ (l→r Hdup H⊆)
    l→r (step-cong Hdup) (sub-consʳ H∉ H⊆)  =
      sub-consʳ (subst (_ ∉_) (dup-raw-dom Hdup) H∉) (l→r (step-cong Hdup) H⊆)
    l→r (step-cong Hdup) (sub-consˡ H∈ H⊆) =
      sub-consˡ (subst (_ ∈_) (dup-raw-dom Hdup) H∈) (l→r Hdup H⊆)
    l→r (step-dup H∈) (sub-cons reflᵢ H∉ H⊆) =
      absurd (is-no-false H∉ (raw-sub→dom-⊆ H⊆ _ H∈))
    l→r (step-dup H∈) (sub-consʳ H∉ H⊆) = absurd (is-no-false H∉ H∈)
    l→r (step-dup H∈) (sub-consˡ _ H⊆)  = H⊆

    r→l : {l l1 l2 : RawEnv X} → dup-step l1 l2 → raw-sub l2 l → raw-sub l1 l
    r→l (step-cong Hdup) (sub-cons reflᵢ H∉ H⊆) = sub-cons reflᵢ H∉ (r→l Hdup H⊆)
    r→l (step-cong Hdup) (sub-consʳ H∉ H⊆)      =
      sub-consʳ (subst (_ ∉_) (sym $ dup-raw-dom Hdup) H∉) (r→l (step-cong Hdup) H⊆)
    r→l (step-cong Hdup) (sub-consˡ H∈ H⊆) =
      sub-consˡ (subst (_ ∈_) (sym $ dup-raw-dom Hdup) H∈) (r→l Hdup H⊆)
    r→l (step-dup H∈) H⊆ = sub-consˡ H∈ H⊆

raw-sub' : {X : Type ℓ} ⦃ _ : H-Level X 2 ⦄ → RawEnv X → Env X → Prop ℓ
raw-sub' l =
  Coeq-rec (λ l' → el! (raw-sub l l')) (λ (_ , _ , Hdup) → n-ua (dup-subr Hdup))

env-sub : {X : Type ℓ} ⦃ _ : H-Level X 2 ⦄ → Env X → Env X → Prop ℓ
env-sub {X = X} Γ Γ' = Coeq-rec (λ l → raw-sub' l Γ')
  (λ (l , l' , Hdup) →
    Coeq-elim-prop {C = λ Γ → dup-step l l' → raw-sub' l Γ ≡ raw-sub' l' Γ}
      (λ _ → hlevel 1) (λ _ Hdup → n-ua (dup-subl Hdup)) Γ' Hdup)
  Γ

instance
  Inclusion-Env : {X : Type ℓ} ⦃ _ : H-Level X 2 ⦄ → Inclusion (Env X) ℓ
  Inclusion-Env = record { _⊆_ = λ Γ Γ' → ⌞ env-sub Γ Γ' ⌟ }

instance
  Membership-Env : {X : Type ℓ} → ⦃ H-Level X 2 ⦄ → Membership (𝔸 × X) (Env X) ℓ
  Membership-Env = record { _∈_ = λ (x , T) Γ → [ x ∶ T ] ⊆ Γ }

infixl 5 _∶_∈_
_∶_∈_ : {X : Type ℓ} → ⦃ H-Level X 2 ⦄ → 𝔸 → X → Env X → Type ℓ
a ∶ T ∈ Γ = (a , T) ∈ Γ

env-⊆-nil : ⦃ _ : H-Level X 2 ⦄ (Γ : Env X) → Γ ⊆ ε → Γ ≡ ε
env-⊆-nil =
  Coeq-elim-prop {C = λ Γ → Γ ⊆ ε → Γ ≡ ε} (λ _ → hlevel 1) λ where
    [] _                      → refl
    (_ ∷ _) (sub-consˡ H∈ H⊆) → absurd (¬mem-[] (raw-sub→dom-⊆ H⊆ _ H∈))

module EnvDenot
  {o ℓ} {C : Precategory o ℓ} (cart : Cartesian-category C)
  (X-denot : X → Precategory.Ob C) where
  private module C = Cartesian-category cart
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

  raw-proj : {l l' : RawEnv X} → is-nubbed l → raw-sub l l' → Hom ⟦ l' ⟧ ⟦ l ⟧
  raw-proj _ sub-nil                         = !
  raw-proj (_ ∷ Hnub) (sub-cons reflᵢ H∉ H⊆) = ⟨ raw-proj Hnub H⊆ C.∘ π₁ , π₂ ⟩
  raw-proj Hnub (sub-consʳ H∉ H⊆)            = raw-proj Hnub H⊆ C.∘ π₁
  raw-proj (H∉ ∷ Hnub) (sub-consˡ H∈ H⊆)     = absurd (is-no-false H∉ H∈)

  env-proj : ⦃ _ : H-Level X 2 ⦄ {Γ Γ' : Env X} → Γ ⊆ Γ' → Hom ⟦ Γ' ⟧ ⟦ Γ ⟧
  env-proj {Γ} {Γ'} H⊆ = raw-proj (env-nub-is-nubbed Γ)
    (subst₂ _⊆_ (env-nub-univ Γ) (env-nub-univ Γ') H⊆)

-- dom-∈ : {Γ : Env X} {x : 𝔸} → x ∈ dom Γ → Σ[ T ∈ X ] (x , T) ∈ Γ
-- dom-∈ = {!!}
-- dom-∈ {Γ = x ∷ Γ} (∈∪₁ ∈[]) = _ , here refl
-- dom-∈ {Γ = x ∷ Γ} (∈∪₂ x∈Γ) with T , H∈ ← dom-∈ x∈Γ = T , there H∈

-- ∈-dom : {x : 𝔸} → (x , T) ∈ˡ Γ → x ∈ dom Γ
-- ∈-dom {Γ = x ∷ Γ} (here refl) = ∈∪₁ ∈[]
-- ∈-dom {Γ = x ∷ Γ} (there H∈)  = ∈∪₂ (∈-dom H∈)

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
