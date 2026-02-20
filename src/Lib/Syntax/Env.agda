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

raw-nub : RawEnv X → RawEnv X
raw-nub []      = []
raw-nub (x ∷ l) =
  ifᵈ holds? (fst x ∈ raw-dom (raw-nub l)) then
    raw-nub l
  else
    x ∷ raw-nub l

raw-map : (X → Y) → RawEnv X → RawEnv Y
raw-map f = map (λ (x , T) → x , f T)

data raw-sub {X : Type ℓ} : RawEnv X → RawEnv X → Type ℓ where
  sub-nil : raw-sub [] l
  sub-cons
    : {x y : 𝔸 × X} → x ≡ᵢ y → fst y ∉ raw-dom l'
    → raw-sub l l' → raw-sub (x ∷ l) (y ∷ l')
  sub-consr
    : {x y : 𝔸 × X} → fst x ∉ raw-dom l
    → raw-sub (x ∷ l) l' → raw-sub (x ∷ l) (y ∷ l')
  sub-consl
    : fst x ∈ raw-dom l
    → raw-sub l l' → raw-sub (x ∷ l) l'

data is-nubbed {X : Type ℓ} : RawEnv X → Type ℓ where
  []  : is-nubbed []
  _∷_ : fst x ∉ raw-dom l → is-nubbed l → is-nubbed (x ∷ l)

raw-dom-++ : (l l' : RawEnv X) → raw-dom (l ++ l') ≡ raw-dom l ∪ raw-dom l'
raw-dom-++ l l' =
  ap from-list (map-++ fst l l') ∙ from-list-++ (map fst l) (map fst l')

raw-dom-nub : (l : RawEnv X) → raw-dom (raw-nub l) ≡ raw-dom l
raw-dom-nub [] = refl
raw-dom-nub (x ∷ l) with holds? (fst x ∈ raw-dom (raw-nub l))
... | yes H∈ = uncons _ _ H∈ ∙ ap (fst x ∷_) (raw-dom-nub l)
... | no  H∉ = ap (fst x ∷_) (raw-dom-nub l)

raw-nub-cons
  : (l : RawEnv X) → a ∉ raw-dom l
  → raw-nub ((a , T) ∷ l) ≡ (a , T) ∷ raw-nub l
raw-nub-cons {a = a} l H∉ = ifᵈ-no (holds? (a ∈ raw-dom (raw-nub l)))
  (subst (a ∉_) (sym $ raw-dom-nub l) H∉)

raw-nub-is-nubbed : (l : RawEnv X) → is-nubbed (raw-nub l)
raw-nub-is-nubbed [] = []
raw-nub-is-nubbed (x ∷ l) with holds? (fst x ∈ raw-dom (raw-nub l))
... | yes _ = raw-nub-is-nubbed l
... | no H∉ = false→is-no H∉ ∷ raw-nub-is-nubbed l

¬is-nubbed-++ : a ∈ raw-dom l → a ∈ raw-dom l' → ¬ is-nubbed (l ++ l')
¬is-nubbed-++ {l = []} H∈ H∈'    = absurd (¬mem-[] H∈)
¬is-nubbed-++ {l = x ∷ l} H∈ H∈' = ∈ᶠˢ-split
  (λ { reflᵢ (H∉ ∷ _) →
    is-no→false (∉∪₂ (raw-dom l) (subst (_ ∉_) (raw-dom-++ l _) H∉)) H∈' })
  (λ { H∈l (_ ∷ Hnub) → ¬is-nubbed-++ H∈l H∈' Hnub })
  H∈

raw-sub→dom-⊆ : raw-sub l l' → raw-dom l ⊆ raw-dom l'
raw-sub→dom-⊆ sub-nil                = λ _ H∈ → absurd (¬mem-[] H∈)
raw-sub→dom-⊆ (sub-cons reflᵢ H∉ H⊆) = λ _ H∈ →
  ∈ᶠˢ-split hereₛ' (λ H∈' → thereₛ (raw-sub→dom-⊆ H⊆ _ H∈')) H∈
raw-sub→dom-⊆ (sub-consr H∉ H⊆) = λ _ H∈ → thereₛ (raw-sub→dom-⊆ H⊆ _ H∈)
raw-sub→dom-⊆ (sub-consl H∈ H⊆) = λ _ H∈' →
  ∈ᶠˢ-split (λ {reflᵢ → raw-sub→dom-⊆ H⊆ _ H∈}) (raw-sub→dom-⊆ H⊆ _) H∈'

-- ∈-raw-mem : a ∈ raw-dom l → ∃[ T ∈ X ] raw-mem a T l
-- ∈-raw-mem {l = []}    H∈ = absurd (¬mem-[] H∈)
-- ∈-raw-mem {l = x ∷ l} H∈ = ∈ᶠˢ-split
--   (λ { reflᵢ → case holds? (fst x ∈ raw-dom l) of λ where
--        (yes H∈') → case ∈-raw-mem H∈' of λ _ H∈'' → inc (_ , consr H∈'')
--        (no  H∉)  → inc (_ , here reflᵢ (false-is-no H∉))
--      })
--   (λ { p → case ∈-raw-mem p of λ _ H∈' → inc (_ , consr H∈') })
--   H∈

raw-sub-is-prop : ⦃ _ : H-Level X 2 ⦄ {l l' : RawEnv X} → is-prop (raw-sub l l')
raw-sub-is-prop sub-nil sub-nil                             = refl
raw-sub-is-prop (sub-cons reflᵢ H∉ H⊆) (sub-cons p H∉' H⊆') = λ i →
  sub-cons (q i) (is-yes-is-prop H∉ H∉' i) (raw-sub-is-prop H⊆ H⊆' i) where
  q : reflᵢ ≡ p
  q = prop!
raw-sub-is-prop (sub-cons reflᵢ H∉ H⊆) (sub-consr _ H⊆') =
  absurd (is-no→false H∉ (raw-sub→dom-⊆ H⊆' _ hereₛ))
raw-sub-is-prop (sub-cons reflᵢ H∉ H⊆) (sub-consl H∈ H⊆') =
  absurd (is-no→false H∉ (raw-sub→dom-⊆ H⊆ _ H∈))
raw-sub-is-prop (sub-consr H∉ H⊆) (sub-cons reflᵢ H∉' H⊆') =
  absurd (is-no→false H∉' (raw-sub→dom-⊆ H⊆ _ hereₛ))
raw-sub-is-prop (sub-consr H∉ H⊆) (sub-consr H∉' H⊆') =
  ap₂ sub-consr (is-yes-is-prop H∉ H∉') (raw-sub-is-prop H⊆ H⊆')
raw-sub-is-prop (sub-consr H∉ H⊆) (sub-consl H∈ H⊆') = absurd (is-no→false H∉ H∈)
raw-sub-is-prop (sub-consl H∈ H⊆) (sub-cons reflᵢ H∉ H⊆') =
  absurd (is-no→false H∉ (raw-sub→dom-⊆ H⊆' _ H∈))
raw-sub-is-prop (sub-consl H∈ H⊆) (sub-consr H∉ H⊆')  = absurd (is-no→false H∉ H∈)
raw-sub-is-prop (sub-consl H∈ H⊆) (sub-consl H∈' H⊆') =
  ap₂ sub-consl prop! (raw-sub-is-prop H⊆ H⊆')

instance
  H-Level-raw-sub
    : ∀ ⦃ _ : H-Level X 2 ⦄ {l l' : RawEnv X} {n} → H-Level (raw-sub l l') (suc n)
  H-Level-raw-sub = basic-instance 1 raw-sub-is-prop

raw-sub-nil-inv : raw-sub l [] → l ≡ []
raw-sub-nil-inv {l = []} _                    = refl
raw-sub-nil-inv {l = _ ∷ _} (sub-consl H∈ H⊆) =
  absurd (¬mem-[] (raw-sub→dom-⊆ H⊆ _ H∈))

raw-sub-consl-inv : raw-sub (x ∷ l) l' → raw-sub l l'
raw-sub-consr     : raw-sub l l' → raw-sub l (x ∷ l')

raw-sub-consl-inv (sub-cons p H∉ H⊆) = raw-sub-consr H⊆
raw-sub-consl-inv (sub-consr H∉ H⊆)  = raw-sub-consr (raw-sub-consl-inv H⊆)
raw-sub-consl-inv (sub-consl H∈ H⊆)  = H⊆

raw-sub-consr {l = []} H⊆ = sub-nil
raw-sub-consr {l = x ∷ l} H⊆ with holds? (fst x ∈ raw-dom l)
... | yes H∈ = sub-consl H∈ (raw-sub-consr (raw-sub-consl-inv H⊆))
... | no  H∉ = sub-consr (false→is-no H∉) H⊆

raw-sub-&r : fst x ∉ raw-dom l → raw-sub l l' → raw-sub l (l' ++ x ∷ [])
raw-sub-&r H∉ sub-nil = sub-nil
raw-sub-&r {l' = _ ∷ l'} H∉ (sub-cons reflᵢ H∉' H⊆) =
  sub-cons reflᵢ
    (subst (_ ∉_) (sym $ raw-dom-++ l' _) (∉∪ H∉' (∉∷ (sym≠ _ _ $ ∉∷₁ H∉) tt)))
    (raw-sub-&r (∉∷₂ H∉) H⊆)
raw-sub-&r H∉ (sub-consr H∉' H⊆) = sub-consr H∉' (raw-sub-&r H∉ H⊆)
raw-sub-&r H∉ (sub-consl H∈ H⊆)  = sub-consl H∈ (raw-sub-&r (∉∷₂ H∉) H⊆)

raw-sub-refl : raw-sub l l
raw-sub-refl {l = []} = sub-nil
raw-sub-refl {l = x ∷ l} with holds? (fst x ∈ raw-dom l)
... | yes H∈ = sub-consl H∈ (raw-sub-consr raw-sub-refl)
... | no  H∉ = sub-cons reflᵢ (false→is-no H∉) raw-sub-refl

raw-sub-trans : {l1 l2 l3 : RawEnv X} → raw-sub l1 l2 → raw-sub l2 l3 → raw-sub l1 l3
raw-sub-trans sub-nil H⊆'                                     = sub-nil
raw-sub-trans (sub-cons reflᵢ H∉ H⊆) (sub-cons reflᵢ H∉' H⊆') =
  sub-cons reflᵢ H∉' (raw-sub-trans H⊆ H⊆')
raw-sub-trans (sub-cons reflᵢ H∉ H⊆) (sub-consr H∉' H⊆') = sub-consr
  (false→is-no λ H∈ → is-no→false H∉ (raw-sub→dom-⊆ H⊆ _ H∈))
  (raw-sub-trans (sub-cons reflᵢ H∉ H⊆) H⊆')
raw-sub-trans (sub-cons reflᵢ H∉ H⊆) (sub-consl H∈ H⊆')  = absurd (is-no→false H∉ H∈)
raw-sub-trans (sub-consr H∉ H⊆) (sub-cons reflᵢ H∉' H⊆') =
  sub-consr H∉ (raw-sub-trans H⊆ H⊆')
raw-sub-trans (sub-consr H∉ H⊆) (sub-consr H∉' H⊆') =
  sub-consr H∉ (raw-sub-trans (sub-consr H∉ H⊆) H⊆')
raw-sub-trans (sub-consr H∉ H⊆) (sub-consl H∈ H⊆') = raw-sub-trans H⊆ H⊆'
raw-sub-trans (sub-consl H∈ H⊆) H⊆' = sub-consl H∈ (raw-sub-trans H⊆ H⊆')

raw-mem-inv : {x y : 𝔸 × X} → raw-sub (x ∷ []) (y ∷ []) → x ≡ᵢ y
raw-mem-inv (sub-cons p _ _)  = p
raw-mem-inv (sub-consr H∉ H⊆) = absurd (¬mem-[] (raw-sub→dom-⊆ H⊆ _ hereₛ))
raw-mem-inv (sub-consl H∈ _)  = absurd (¬mem-[] H∈)

raw-mem-++r : fst x ∈ raw-dom l' → raw-sub (x ∷ []) (l ++ l') → raw-sub (x ∷ []) l'
raw-mem-++r {l = []} H∈ H⊆ = H⊆
raw-mem-++r {l = y ∷ l} H∈ (sub-cons reflᵢ H∉ H⊆) =
  absurd (is-no→false (∉∪₂ (raw-dom l) (subst (_ ∉_) (raw-dom-++ l _) H∉)) H∈)
raw-mem-++r {l = y ∷ l} H∈ (sub-consr H∉ H⊆)  = raw-mem-++r H∈ H⊆
raw-mem-++r {l = y ∷ l} H∈ (sub-consl H∈' H⊆) = sub-consl H∈' sub-nil

raw-mem-++l : fst x ∉ raw-dom l' → raw-sub (x ∷ []) (l ++ l') → raw-sub (x ∷ []) l
raw-mem-++l {l = []} H∉ H⊆ = absurd (is-no→false H∉ (raw-sub→dom-⊆ H⊆ _ hereₛ))
raw-mem-++l {l = x ∷ l} H∉ (sub-cons reflᵢ H∉' H⊆) =
  sub-cons reflᵢ (∉∪₁ (subst (_ ∉_) (raw-dom-++ l _) H∉')) sub-nil
raw-mem-++l {l = x ∷ l} H∉ (sub-consr H∉' H⊆) = sub-consr tt (raw-mem-++l H∉ H⊆)
raw-mem-++l {l = x ∷ l} H∉ (sub-consl H∈ H⊆)  = sub-consl H∈ sub-nil

raw-sub-strengthen :
  (_ : fst x ∉ raw-dom l)
  (_ : raw-sub l (l' ++ x ∷ []))
  → ----------------------------
  raw-sub l l'
raw-sub-strengthen {l' = []} H∉ sub-nil = sub-nil
raw-sub-strengthen {l' = []} () (sub-cons reflᵢ _ H⊆)
raw-sub-strengthen {l' = []} H∉ (sub-consr _ H⊆) = H⊆
raw-sub-strengthen {l' = []} H∉ (sub-consl H∈ H⊆) = sub-consl H∈
  $ raw-sub-strengthen (∉∷₂ H∉) H⊆
raw-sub-strengthen {l' = y ∷ l'} H∉ sub-nil = sub-nil
raw-sub-strengthen {x = x} {l' = y ∷ l'} H∉ (sub-cons reflᵢ H∉' H⊆) =
  sub-cons reflᵢ (∉∪₁ (subst (_ ∉_) (raw-dom-++ l' (x ∷ [])) H∉'))
  $ raw-sub-strengthen (∉∷₂ H∉) H⊆
raw-sub-strengthen {l' = y ∷ l'} H∉ (sub-consr H∉' H⊆) = sub-consr H∉'
  $ raw-sub-strengthen H∉ H⊆
raw-sub-strengthen {l' = y ∷ l'} H∉ (sub-consl H∈ H⊆) = sub-consl H∈
  $ raw-sub-strengthen (∉∷₂ H∉) H⊆

raw-sub-split :
  (_ : is-nubbed l)
  (_ : fst x ∈ raw-dom l)
  (_ : raw-sub l (l' ++ x ∷ []))
  → --------------------------------------------
  Σ _ λ l'' → raw-sub l'' l' × l ≡ l'' ++ x ∷ []
raw-sub-split {l' = []} Hnub H∈ sub-nil                = absurd (¬mem-[] H∈)
raw-sub-split {l' = []} Hnub H∈ (sub-cons reflᵢ H∉ H⊆) =
  [] , sub-nil , ap (_ ∷_) (raw-sub-nil-inv H⊆)
raw-sub-split {l' = []} Hnub H∈ (sub-consr H∉ H⊆) =
  absurd (¬mem-[] (raw-sub→dom-⊆ H⊆ _ hereₛ))
raw-sub-split {l' = []} (H∉ ∷ Hnub) H∈ (sub-consl {x = y} H∈' H⊆) =
  absurd (is-no→false H∉ H∈')
raw-sub-split {l' = y ∷ l'} Hnub H∈ sub-nil = absurd (¬mem-[] H∈)
raw-sub-split {l = _ ∷ l} {x} {y ∷ l'} (_ ∷ Hnub) H∈ (sub-cons reflᵢ H∉ H⊆) =
  let H≠ : fst y ≠ fst x
      H≠ = ∉∷₁ (∉∪₂ (raw-dom l') (subst (_ ∉_) (raw-dom-++ l' _) H∉))
      H∈' : fst x ∈ raw-dom l
      H∈' = ∈ᶠˢ-split (λ p → absurd (≠→¬≡ H≠ (sym $ Id≃path.to p))) id H∈
      l'' , H⊆' , Heq = raw-sub-split Hnub H∈' H⊆
  in  y ∷ l''
    , sub-cons reflᵢ (∉∪₁ (subst (_ ∉_) (raw-dom-++ l' _) H∉)) H⊆'
    , ap (y ∷_) Heq
raw-sub-split {l' = y ∷ l'} Hnub H∈ (sub-consr H∉ H⊆) =
  let l'' , H⊆' , Heq = raw-sub-split Hnub H∈ H⊆
  in  l'' , raw-sub-consr H⊆' , Heq
raw-sub-split {l' = y ∷ l'} (H∉₀ ∷ Hnub) H∈ (sub-consl H∈' H⊆) =
  absurd (is-no→false H∉₀ H∈')


-- Two environments are related under dup-step precisely if the second
-- is the result of removing a single duplicate key from the first.
data dup-step {X : Type ℓ} : RawEnv X → RawEnv X → Type ℓ where
  step-cong : dup-step l l' → dup-step (x ∷ l) (x ∷ l')
  step-dup  : fst x ∈ raw-dom l → dup-step (x ∷ l) l

private
  dup-raw-dom : dup-step l l' → raw-dom l ≡ raw-dom l'
  dup-raw-dom (step-cong Hdup) = ap (_ ∷_) (dup-raw-dom Hdup)
  dup-raw-dom (step-dup  H∈)   = sym $ uncons _ _ H∈

  step-++ₗ : {l1 : RawEnv X} → dup-step l l' → dup-step (l1 ++ l) (l1 ++ l')
  step-++ₗ {l1 = []}    Hdup = Hdup
  step-++ₗ {l1 = _ ∷ _} Hdup = step-cong (step-++ₗ Hdup)

  step-++ᵣ : {l1 : RawEnv X} → dup-step l l' → dup-step (l ++ l1) (l' ++ l1)
  step-++ᵣ (step-cong Hdup) = step-cong (step-++ᵣ Hdup)
  step-++ᵣ {l' = l'} {l1} (step-dup H∈) =
    step-dup $ subst (_ ∈ᶠˢ_) (sym $ raw-dom-++ l' l1) (unionl-∈ᶠˢ _ _ _ H∈)

  step-raw-map : {f : X → Y} → dup-step l l' → dup-step (raw-map f l) (raw-map f l')
  step-raw-map (step-cong Hdup) = step-cong (step-raw-map Hdup)
  step-raw-map (step-dup {x = x} H∈) = step-dup
    $ subst (fst x ∈_) (ap from-list (sym $ map-comp _ _ _)) H∈

  dup-raw-nub : dup-step l l' → raw-nub l ≡ raw-nub l'
  dup-raw-nub (step-cong {x = x} Hdup) =
    ap (λ l → ifᵈ (holds? (fst x ∈ raw-dom l)) then l else x ∷ l) (dup-raw-nub Hdup)
  dup-raw-nub (step-dup  {x = x} {l} H∈) =
    ifᵈ-yes (holds? (fst x ∈ raw-dom (raw-nub l)))
      (true→is-yes (subst (fst x ∈_) (sym $ raw-dom-nub l) H∈))

  dup-subr
    : ⦃ _ : H-Level X 2 ⦄ {l l1 l2 : RawEnv X}
    → dup-step l1 l2 → raw-sub l l1 ≃ raw-sub l l2
  dup-subr Hdup = prop-ext! (l→r Hdup) (r→l Hdup) where
    l→r : {l l1 l2 : RawEnv X} → dup-step l1 l2 → raw-sub l l1 → raw-sub l l2
    l→r (step-cong Hdup) sub-nil            = sub-nil
    l→r (step-cong Hdup) (sub-cons p H∉ H⊆) =
      sub-cons p (subst (_ ∉_) (dup-raw-dom Hdup) H∉) (l→r Hdup H⊆)
    l→r (step-cong Hdup) (sub-consr H∉ H⊆) = sub-consr H∉ (l→r Hdup H⊆)
    l→r (step-cong Hdup) (sub-consl H∈ H⊆) = sub-consl H∈ (l→r (step-cong Hdup) H⊆)
    l→r (step-dup H∈) sub-nil             = sub-nil
    l→r (step-dup H∈) (sub-cons p H∉ H⊆)  = absurd (is-no→false H∉ H∈)
    l→r (step-dup H∈) (sub-consr _ H⊆)    = H⊆
    l→r (step-dup H∈) (sub-consl H∈' H⊆)  = sub-consl H∈' (l→r (step-dup H∈) H⊆)

    r→l : {l l1 l2 : RawEnv X} → dup-step l1 l2 → raw-sub l l2 → raw-sub l l1
    r→l (step-cong Hdup) sub-nil            = sub-nil
    r→l (step-cong Hdup) (sub-cons p H∉ H⊆) =
      sub-cons p (subst (_ ∉_) (sym $ dup-raw-dom Hdup) H∉) (r→l Hdup H⊆)
    r→l (step-cong Hdup) (sub-consr H∉ H⊆)   = sub-consr H∉ (r→l Hdup H⊆)
    r→l (step-cong Hdup) (sub-consl H∈ H⊆)   = sub-consl H∈ (r→l (step-cong Hdup) H⊆)
    r→l (step-dup H∈) sub-nil                = sub-nil
    r→l (step-dup H∈) (sub-cons reflᵢ H∉ H⊆) = sub-consr
      (false→is-no λ H∈ → is-no→false H∉ (raw-sub→dom-⊆ H⊆ _ H∈))
      (sub-cons reflᵢ H∉ H⊆)
    r→l (step-dup H∈) (sub-consr H∉ H⊆)  = sub-consr H∉ (sub-consr H∉ H⊆)
    r→l (step-dup H∈) (sub-consl H∈' H⊆) = sub-consl H∈' (r→l (step-dup H∈) H⊆)

  dup-subl
    : ⦃ _ : H-Level X 2 ⦄ {l l1 l2 : RawEnv X}
    → dup-step l1 l2 → raw-sub l1 l ≃ raw-sub l2 l
  dup-subl {X = X} Hdup = prop-ext! (l→r Hdup) (r→l Hdup) where
    l→r : {l l1 l2 : RawEnv X} → dup-step l1 l2 → raw-sub l1 l → raw-sub l2 l
    l→r (step-cong Hdup) (sub-cons p H∉ H⊆) = sub-cons p H∉ (l→r Hdup H⊆)
    l→r (step-cong Hdup) (sub-consr H∉ H⊆)  =
      sub-consr (subst (_ ∉_) (dup-raw-dom Hdup) H∉) (l→r (step-cong Hdup) H⊆)
    l→r (step-cong Hdup) (sub-consl H∈ H⊆) =
      sub-consl (subst (_ ∈_) (dup-raw-dom Hdup) H∈) (l→r Hdup H⊆)
    l→r (step-dup H∈) (sub-cons reflᵢ H∉ H⊆) =
      absurd (is-no→false H∉ (raw-sub→dom-⊆ H⊆ _ H∈))
    l→r (step-dup H∈) (sub-consr H∉ H⊆) = absurd (is-no→false H∉ H∈)
    l→r (step-dup H∈) (sub-consl _ H⊆)  = H⊆

    r→l : {l l1 l2 : RawEnv X} → dup-step l1 l2 → raw-sub l2 l → raw-sub l1 l
    r→l (step-cong Hdup) (sub-cons reflᵢ H∉ H⊆) = sub-cons reflᵢ H∉ (r→l Hdup H⊆)
    r→l (step-cong Hdup) (sub-consr H∉ H⊆)      =
      sub-consr (subst (_ ∉_) (sym $ dup-raw-dom Hdup) H∉) (r→l (step-cong Hdup) H⊆)
    r→l (step-cong Hdup) (sub-consl H∈ H⊆) =
      sub-consl (subst (_ ∈_) (sym $ dup-raw-dom Hdup) H∈) (r→l Hdup H⊆)
    r→l (step-dup H∈) H⊆ = sub-consl H∈ H⊆

-- We form the type of proper environments as the quotient of RawEnv under dup-step.
Env : Type ℓ → Type ℓ
Env X = RawEnv X / dup-step

private variable
  Γ Γ' : Env X

env-case
  : ∀ {C : Env X → Type ℓ} ⦃ _ : ∀ {x} → H-Level (C x) 1 ⦄
  → (∀ l → C (inc l))
  → ∀ Γ → C Γ
env-case {C = C} = Coeq-elim-prop {C = C} (λ _ → hlevel 1)

env-rec
  : ∀ {C : Type ℓ} ⦃ _ : H-Level C 2 ⦄
  → (h : RawEnv X → C)
  → (∀ {l l'} → dup-step l l' → h l ≡ h l') → Env X → C
env-rec h Heq = Coeq-rec h λ (_ , _ , Hdup) → Heq Hdup

env-cons : (𝔸 × X) → Env X → Env X
env-cons x = env-rec (λ l → inc (x ∷ l)) (quot ∘ step-cong)

pattern ε         = inc []
pattern [_∶_] x T = inc ((x , T) ∷ [])

infixl 8 _,_∶_
_,_∶_ : Env X → 𝔸 → X → Env X
Γ , a ∶ T = env-cons (a , T) Γ

env-dom : Env X → Finset 𝔸
env-dom = env-rec raw-dom dup-raw-dom

env-dom-cons : ∀ Γ → env-dom (Γ , a ∶ T) ≡ [ a ] ∪ env-dom Γ
env-dom-cons {a = a} {T = T} = env-case (λ _ → refl)

env-cons-∈ : a ∈ env-dom Γ → (Γ , a ∶ T) ≡ Γ
env-cons-∈ {Γ = Γ} =
  env-case {C = λ Γ → ∀ {a T} → a ∈ env-dom Γ → (Γ , a ∶ T) ≡ Γ}
    (λ l H∈ → quot (step-dup H∈)) Γ

opaque
  env-append' : RawEnv X → Env X → Env X
  env-append' l = env-rec (λ l' → inc (l ++ l')) (quot ∘ step-++ₗ)

  env-append : Env X → Env X → Env X
  env-append Γ Γ' =
    env-rec (λ l → env-append' l Γ')
      (env-case {C = λ Γ → dup-step _ _ → env-append' _ Γ ≡ env-append' _ Γ}
        (λ _ → quot ∘ step-++ᵣ) Γ')
      Γ

  infixl 8 _&_
  _&_ : Env X → Env X → Env X
  Γ & Γ' = env-append Γ' Γ

  env-dom-& : (Γ Γ' : Env X) → env-dom (Γ' & Γ) ≡ env-dom Γ ∪ env-dom Γ'
  env-dom-& =
    env-case λ l  →
    env-case λ l' →
    raw-dom-++ l l'

  env-&-idl : (Γ : Env X) → Γ & ε ≡ Γ
  env-&-idl = env-case λ _ → refl

  env-cons-& : (Γ₁ Γ₂ : Env X) → env-cons x (Γ₁ & Γ₂) ≡ Γ₁ & env-cons x Γ₂
  env-cons-& =
    env-case λ _ →
    env-case λ _ →
    refl

  env-&-cons : (Γ : Env X) → Γ , a ∶ T ≡ Γ & [ a ∶ T ]
  env-&-cons = env-case λ _ → refl

env-nub : ⦃ H-Level X 2 ⦄ → Env X → RawEnv X
env-nub = env-rec raw-nub dup-raw-nub

inc-raw-nub : (l : RawEnv X) → Path (Env X) (inc l) (inc (raw-nub l))
inc-raw-nub [] = refl
inc-raw-nub (x ∷ l) with holds? (fst x ∈ raw-dom (raw-nub l))
... | yes H∈ = env-cons-∈ (subst (fst x ∈_) (raw-dom-nub l) H∈) ∙ inc-raw-nub l
... | no  _  = ap (env-cons x) (inc-raw-nub l)

env-nub-univ : ⦃ _ : H-Level X 2 ⦄ (Γ : Env X) → Γ ≡ inc (env-nub Γ)
env-nub-univ = env-case inc-raw-nub

env-nub-is-nubbed : ⦃ _ : H-Level X 2 ⦄ (Γ : Env X) → is-nubbed (env-nub Γ)
env-nub-is-nubbed Γ = subst (is-nubbed ∘ env-nub)
  (sym $ env-nub-univ Γ) (raw-nub-is-nubbed (env-nub Γ))

env-nub-cons
  : ⦃ _ : H-Level X 2 ⦄ (Γ : Env X)
  → a ∉ env-dom Γ → env-nub (Γ , a ∶ T) ≡ (a , T) ∷ env-nub Γ
env-nub-cons = env-case raw-nub-cons

env-map : (X → Y) → Env X → Env Y
env-map f = env-rec (λ l → inc (raw-map f l)) (quot ∘ step-raw-map)

opaque
  env-sub' : {X : Type ℓ} ⦃ _ : H-Level X 2 ⦄ → RawEnv X → Env X → Prop ℓ
  env-sub' l = env-rec (λ l' → el! (raw-sub l l')) (n-ua ∘ dup-subr)

  env-sub : {X : Type ℓ} ⦃ _ : H-Level X 2 ⦄ → Env X → Env X → Prop ℓ
  env-sub {X = X} Γ Γ' =
    env-rec (λ l → env-sub' l Γ')
      (env-case {C = λ Γ → dup-step _ _ → env-sub' _ Γ ≡ env-sub' _ Γ}
        (λ _ Hdup → n-ua (dup-subl Hdup)) Γ')
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

opaque
  unfolding env-sub env-append
  env-sub-nil : ⦃ _ : H-Level X 2 ⦄ {Γ : Env X} → ε ⊆ Γ
  env-sub-nil {Γ = Γ} = env-case {C = ε ⊆_} (λ _ → sub-nil) Γ

  env-sub-cons
    : ⦃ _ : H-Level X 2 ⦄ {Γ Γ' : Env X} {x y : 𝔸 × X}
    → x ≡ᵢ y → fst y ∉ env-dom Γ' → Γ ⊆ Γ' → env-cons x Γ ⊆ env-cons y Γ'
  env-sub-cons {Γ = Γ} {Γ'} {x} {y} = pres Γ Γ' where
    pres
      : ∀ Γ Γ' → x ≡ᵢ y → fst y ∉ env-dom Γ' → Γ ⊆ Γ' → env-cons x Γ ⊆ env-cons y Γ'
    pres = env-case λ _ → env-case λ _ → sub-cons

  env-sub-nil-inv : ⦃ _ : H-Level X 2 ⦄ (Γ : Env X) → Γ ⊆ ε → Γ ≡ ε
  env-sub-nil-inv = env-case {C = λ Γ → Γ ⊆ ε → Γ ≡ ε} λ _ → ap inc ∘ raw-sub-nil-inv

  env-sub-consr
    : ⦃ _ : H-Level X 2 ⦄ {Γ Γ' : Env X} {x : 𝔸 × X}
    → Γ ⊆ Γ' → Γ ⊆ env-cons x Γ'
  env-sub-consr {Γ = Γ} {Γ'} {x} = consr Γ Γ' where
    consr : ∀ Γ Γ' → Γ ⊆ Γ' → Γ ⊆ env-cons x Γ'
    consr = env-case λ _ → env-case λ _ → raw-sub-consr

  env-sub-&r
    : ⦃ _ : H-Level X 2 ⦄ {Γ Γ' : Env X} {a : 𝔸} {T : X}
    → a ∉ env-dom Γ → Γ ⊆ Γ' → Γ ⊆ ([ a ∶ T ] & Γ')
  env-sub-&r {Γ = Γ} {Γ'} {a} {T} = sub Γ Γ' where
    sub : ∀ Γ Γ' → a ∉ env-dom Γ → Γ ⊆ Γ' → Γ ⊆ ([ a ∶ T ] & Γ')
    sub = env-case λ _ → env-case λ _ → raw-sub-&r

  env-sub→dom-⊆
    : ⦃ _ : H-Level X 2 ⦄ {Γ Γ' : Env X}
    → Γ ⊆ Γ' → env-dom Γ ⊆ env-dom Γ'
  env-sub→dom-⊆ {X = X} {Γ = Γ} {Γ'} = sub Γ Γ' where
    sub : (Γ Γ' : Env X) → Γ ⊆ Γ' → env-dom Γ ⊆ env-dom Γ'
    sub = env-case λ _ → env-case λ _ → raw-sub→dom-⊆

  env-sub-refl : ⦃ _ : H-Level X 2 ⦄ {Γ : Env X} → Γ ⊆ Γ
  env-sub-refl {X = X} {Γ = Γ} = refl_ Γ where
    refl_ : (Γ : Env X) → Γ ⊆ Γ
    refl_ = env-case λ _ → raw-sub-refl

  env-sub-trans : ⦃ _ : H-Level X 2 ⦄ {Γ1 Γ2 Γ3 : Env X} → Γ1 ⊆ Γ2 → Γ2 ⊆ Γ3 → Γ1 ⊆ Γ3
  env-sub-trans {X = X} {Γ1 = Γ1} {Γ2} {Γ3} = trans Γ1 Γ2 Γ3 where
    trans : (Γ1 Γ2 Γ3 : Env X) → Γ1 ⊆ Γ2 → Γ2 ⊆ Γ3 → Γ1 ⊆ Γ3
    trans = env-case λ _ → env-case λ _ → env-case λ _ → raw-sub-trans

  env-mem-inv
    : ⦃ _ : H-Level X 2 ⦄ {a b : 𝔸} {T T' : X}
    → [ a ∶ T ] ⊆ [ b ∶ T' ] → (a , T) ≡ᵢ (b , T')
  env-mem-inv = raw-mem-inv

  env-mem-++r
    : ⦃ _ : H-Level X 2 ⦄ {Γ Γ' : Env X} {x : 𝔸 × X}
    → fst x ∈ env-dom Γ' → x ∈ (Γ' & Γ) → x ∈ Γ'
  env-mem-++r {X = X} {Γ} {Γ'} {x} = mem Γ Γ' where
    mem : ∀ Γ Γ' → fst x ∈ env-dom Γ' → x ∈ (Γ' & Γ) → x ∈ Γ'
    mem = env-case λ _ → env-case λ _ → raw-mem-++r

  env-mem-++l
    : ⦃ _ : H-Level X 2 ⦄ {Γ Γ' : Env X} {x : 𝔸 × X}
    → fst x ∉ env-dom Γ' → x ∈ (Γ' & Γ) → x ∈ Γ
  env-mem-++l {X = X} {Γ} {Γ'} {x} = mem Γ Γ' where
    mem : ∀ Γ Γ' → fst x ∉ env-dom Γ' → x ∈ (Γ' & Γ) → x ∈ Γ
    mem = env-case λ _ → env-case λ _ → raw-mem-++l

  env-mem-nub
    : ⦃ _ : H-Level X 2 ⦄ {Γ : Env X} {x : 𝔸 × X}
    → raw-sub (x ∷ []) (env-nub Γ)
    → x ∈ Γ
  env-mem-nub {Γ = Γ} H∈ = subst (_ ∈_) (sym (env-nub-univ Γ)) H∈

  env-sub-strengthen :
    ⦃ _ : H-Level X 2 ⦄
    {Γ Γ' : Env X}
    {a : 𝔸} {T : X}
    (_ : a ∉ env-dom Γ)
    (_ : Γ ⊆ ([ a ∶ T ] & Γ'))
    → ---------------------------
    Γ ⊆ Γ'
  env-sub-strengthen {X = X} {Γ} {Γ'} {a} {T} = strengthen Γ Γ' where
    strengthen : ∀ Γ Γ' → a ∉ env-dom Γ → Γ ⊆ ([ a ∶ T ] & Γ') → Γ ⊆ Γ'
    strengthen = env-case λ _ → env-case λ _ → raw-sub-strengthen

  env-sub-split :
    ⦃ _ : H-Level X 2 ⦄
    {Γ Γ' : Env X}
    {a : 𝔸} {T : X}
    (_ : a ∈ env-dom Γ)
    (_ : Γ ⊆ ([ a ∶ T ] & Γ'))
    → ----------------------------------------------------------
    Σ _ λ Γ'' → Γ'' ⊆ Γ' × Γ ≡ [ a ∶ T ] & Γ'' × a ∉ env-dom Γ''
  env-sub-split {Γ = Γ} {Γ'} H∈ H⊆
    rewrite Id≃path.from (env-nub-univ Γ)
          | Id≃path.from (env-nub-univ Γ') =
    let l , H⊆ , Heq = raw-sub-split (env-nub-is-nubbed Γ) H∈ H⊆
    in  inc l , H⊆ , ap inc Heq , false→is-no λ H∈ →
      ¬is-nubbed-++ H∈ hereₛ (subst is-nubbed Heq (env-nub-is-nubbed Γ))


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
  raw-proj Hnub (sub-consr H∉ H⊆)            = raw-proj Hnub H⊆ C.∘ π₁
  raw-proj (H∉ ∷ Hnub) (sub-consl H∈ H⊆)     = absurd (is-no→false H∉ H∈)

  opaque
    unfolding env-sub
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
