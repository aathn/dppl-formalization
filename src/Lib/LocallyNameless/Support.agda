--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.LocallyNameless.Support where

open import Lib.Prelude
open import Lib.Data.Dec
open import Lib.Data.Finset
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets
open import Lib.LocallyNameless.Freshness
open import Lib.LocallyNameless.LocalClosedness

open import Data.Nat.Base using (suc-inj)
open import Data.Nat.Order using (<-not-equal ; <-from-not-≤ ; <-from-≤)

open FinsetSyntax
open NatOrd

----------------------------------------------------------------------
-- Locally nameless sets [Definition 2.9]
----------------------------------------------------------------------
record lns (X : Type) : Type where
  constructor mklns
  field
    ⦃ ocSet ⦄ : oc X
    asupp : (x : X) → И[ a ∈ 𝔸 ] a # x
    isupp : (x : X) → Σ[ i ∈ Nat ] (i ≻ x)

open lns ⦃ ... ⦄ public

infix 4 _atom-supports_
_atom-supports_ :
  {X : Type}
  ⦃ _ : oc X ⦄
  (A : Finset 𝔸)
  (x : X)
  → ----------
  Type
A atom-supports x = ∀ a → a ∉ A → a # x

----------------------------------------------------------------------
-- Locally nameless set of indices and atoms [Example 2.10]
----------------------------------------------------------------------
lnsNat𝔸 : lns Nat𝔸
ocSet ⦃ lnsNat𝔸 ⦄ = ocNat𝔸
asupp ⦃ lnsNat𝔸 ⦄ (inl i) = Иi Ø λ _ → refl
asupp ⦃ lnsNat𝔸 ⦄ (inr a) = Иi [ a ] и₂
  where
  и₂ : (b : 𝔸)⦃ _ : b ∉ [ a ] ⦄ → b # inr a
  и₂ b ⦃ p ⦄ = ifᵈ-no (b ≡? a) (∉∷₁ auto)
isupp ⦃ lnsNat𝔸 ⦄ (inl i) = (suc i , s₂)
  where
  s₂ : suc i ≻ inl i
  s₂ j ⦃ p ⦄ = new Ø , ifᵈ-≠ (<-not-equal p ∘ sym)
isupp ⦃ lnsNat𝔸 ⦄ (inr a) = (0 , λ _ → (a , refl))

----------------------------------------------------------------------
-- Lambda terms [Example 2.11]
----------------------------------------------------------------------
module LambdaTerm where
  data Lam : Type where
    var : Nat𝔸 → Lam
    lam : Lam → Lam
    app : Lam × Lam → Lam

  pattern bvar i = var (inl i)
  pattern fvar a = var (inr a)

  lam-inj : ∀{t t'} → lam t ≡ lam t' → t ≡ t'
  lam-inj {t} p = ap f p where
    f = λ {(lam t) → t ; _ → t}

  app-inj :
    {t₁ t₂ t₁' t₂' : Lam}
    (_ : app(t₁ , t₂) ≡ app(t₁' , t₂'))
    → ---------------------------------
    (t₁ ≡ t₁') × (t₂ ≡ t₂')
  app-inj {t₁} p = ap f₁ p , ap f₂ p where
    f₁ = λ {(app(t₁ , _)) → t₁ ; _ → t₁}
    f₂ = λ {(app(_ , t₂)) → t₂ ; _ → t₁}

  bvar≠fvar : ∀{i a} → ¬ bvar i ≡ fvar a
  bvar≠fvar p = subst distinguish p tt where
    distinguish : Lam → Type
    distinguish (bvar _) = ⊤
    distinguish (fvar _) = ⊥
    distinguish _ = ⊤

  -- Lam is an oc-set
  instance
    ocLam : oc Lam
    ocLam = mkoc opn cls ax₁ ax₂ ax₃ ax₄ ax₅ ax₆ ax₇ ax₈ ax₉
      where
      X = Lam
      opn : Nat → 𝔸 → X → X
      opn i a (var v)   = var ((i ~> a) v)
      opn i a (lam t) = lam(opn (suc i) a t)
      opn i a (app(t , t')) = app(opn i a t , opn i a t')
      cls : Nat → 𝔸 → X → X
      cls i a (var v)   = var ((i <~ a) v)
      cls i a (lam t) = lam(cls (suc i) a t)
      cls i a (app(t , t')) = app(cls i a t , cls i a t')
      ax₁ :
        (i : Nat)
        (a b : 𝔸)
        (t : X)
        → -----------------------------
        opn i a (opn i b t) ≡ opn i b t
      ax₁ i a b (var v) = ap var (oc₁ i a b v)
      ax₁ i a b (lam t) = ap lam (ax₁ (suc i) a b t)
      ax₁ i a b (app(t , t')) =
        ap app $ ap₂ _,_ (ax₁ i a b t) (ax₁ i a b t')
      ax₂ :
        (i j : Nat)
        (a : 𝔸)
        (t : X)
        → -----------------------------
        cls i a (cls j a t) ≡ cls j a t
      ax₂ i j a (var v) = ap var (oc₂ i j a v)
      ax₂ i j a (lam t) = ap lam (ax₂ (suc i) (suc j) a t)
      ax₂ i j a (app(t , t')) =
        ap app $ ap₂ _,_ (ax₂ i j a t) (ax₂ i j a t')
      ax₃ :
        (i : Nat)
        (a : 𝔸)
        (t : X)
        → -----------------------------
        cls i a (opn i a t) ≡ cls i a t
      ax₃ i a (var v) = ap var (oc₃ i a v)
      ax₃ i a (lam t) = ap lam (ax₃ (suc i) a t)
      ax₃ i a (app(t , t')) =
        ap app $ ap₂ _,_ (ax₃ i a t) (ax₃ i a t')
      ax₄ :
        (i : Nat)
        (a : 𝔸)
        (t : X)
        → -----------------------------
          opn i a (cls i a t) ≡ opn i a t
      ax₄ i a (var v) = ap var (oc₄ i a v)
      ax₄ i a (lam t) = ap lam (ax₄ (suc i) a t)
      ax₄ i a (app(t , t')) =
        ap app $ ap₂ _,_ (ax₄ i a t) (ax₄ i a t')
      ax₅ :
        (i j : Nat)
        (a b : 𝔸)
        (t : X)
        ⦃ _ : i ≠ j ⦄
        → ---------------------------------------
        opn i a (opn j b t) ≡ opn j b (opn i a t)
      ax₅ i j a b (var v) = ap var (oc₅ i j a b v)
      ax₅ i j a b (lam t) =
        ap lam (ax₅ (suc i) (suc j) a b t ⦃ inj≠ suc-inj auto ⦄)
      ax₅ i j a b  (app(t , t')) =
        ap app $ ap₂ _,_ (ax₅ i j a b t) (ax₅ i j a b t')
      ax₆ :
        (i j : Nat)
        (a b : 𝔸)
        (t : X)
          ⦃ _ : a ≠ b ⦄
        → ---------------------------------------
        cls i a (cls j b t) ≡ cls j b (cls i a t)
      ax₆ i j a b (var v) = ap var (oc₆ i j a b v)
      ax₆ i j a b (lam t) = ap lam (ax₆ (suc i) (suc j) a b t)
      ax₆ i j a b (app(t , t')) =
        ap app $ ap₂ _,_ (ax₆ i j a b t) (ax₆ i j a b t')
      ax₇ :
        (i j : Nat)
        (a b : 𝔸)
        (t : X)
        ⦃ _ : i ≠ j ⦄
        ⦃ _ : a ≠ b ⦄
        → ---------------------------------------
          opn i a (cls j b t) ≡ cls j b (opn i a t)
      ax₇ i j a b (var v) = ap var (oc₇ i j a b v)
      ax₇ i j a b (lam t) =
        ap lam (ax₇ (suc i) (suc j) a b t ⦃ inj≠ suc-inj auto ⦄)
      ax₇ i j a b (app(t , t')) =
        ap app $ ap₂ _,_ (ax₇ i j a b t) (ax₇ i j a b t')
      ax₈ :
        (i j : Nat)
        (a b : 𝔸)
        (t : X)
        → -----------------------------------------------------------
        opn i b (cls i a (opn j b t)) ≡ opn j b (cls j a (opn i a t))
      ax₈ i j a b (var v) = ap var (oc₈ i j a b v)
      ax₈ i j a b (lam t) = ap lam (ax₈ (suc i) (suc j) a b t)
      ax₈ i j a b (app(t , t')) =
        ap app $ ap₂ _,_ (ax₈ i j a b t) (ax₈ i j a b t')
      ax₉ :
        (i j : Nat)
        (a b : 𝔸)
        (t : X)
        → -----------------------------------------------------------
        cls j a (opn i a (cls j b t)) ≡ cls j b (opn i b (cls i a t))
      ax₉ i j a b (var v) = ap var (oc₉ i j a b v)
      ax₉ i j a b (lam t) = ap lam (ax₉ (suc i) (suc j) a b t)
      ax₉ i j a b (app(t , t')) =
        ap app $ ap₂ _,_ (ax₉ i j a b t) (ax₉ i j a b t')


  -- Free variables defined inductively
  fv : Lam → Finset 𝔸
  fv (bvar _)      = Ø
  fv (fvar a)      = [ a ]
  fv (lam t)       = fv t
  fv (app(t , t')) = fv t ∪ fv t'

  -- Freshness coincides with "not-a-free-variable-of"
  -- (cf. Proposition 4.2)
  fas₁ :
    (t : Lam)
    (a : 𝔸)
    (_ : a ∉ fv t)
    → ------------
    a # t
  fas₁ (bvar i) a p = refl
  fas₁ (fvar b) a _ with no _ ← a ≡? b = refl
  fas₁ (lam t) a p = ap lam p'
    where
    p' : (1 <~ a)t ≡ t
    p' =
      (1 <~ a)t           ≡˘⟨ ap (1 <~ a) (fas₁ t a p) ⟩
      (1 <~ a)((0 <~ a)t) ≡⟨ oc₂ 1 0 a t ⟩
        (0 <~ a)t         ≡⟨ fas₁ t a p ⟩
        t                 ∎
  fas₁ (app(t , t')) a p =
    ap app $ ap₂ _,_ (fas₁ t a (∉∪₁ p)) (fas₁ t' a (∉∪₂ (fv t) p))

  fas₂ :
    (t : Lam)
    (a : 𝔸)
    (_ : a # t)
    → ---------
    a ∉ fv t
  fas₂ (bvar _) _ _ = tt
  fas₂ (fvar b) a p with a ≡? b
  fas₂ (fvar b) _ p  | no _  = tt
  fas₂ (fvar b) _ p  | yes _ = bvar≠fvar p
  fas₂ (lam t) a p = fas₂ t a p'
    where
    p' : (0 <~ a)t ≡ t
    p' =
      (0 <~ a)t           ≡˘⟨ ap (0 <~ a) (lam-inj p) ⟩
      (0 <~ a)((1 <~ a)t) ≡⟨ oc₂ 0 1 a t ⟩
      (1 <~ a)t           ≡⟨ lam-inj p ⟩
      t                   ∎
  fas₂ (app(t , t')) a p =
    ∉∪ (fas₂ t  a (fst (app-inj p))) (fas₂ t' a (snd (app-inj p)))

  -- Inductive closed-at-level predicate
  data lc-at : Nat → Lam → Type where
    lc-at-bvar :
      {i j : Nat}
      ⦃ _ : j < i ⦄
      → --------------
      lc-at i (bvar j)
    lc-at-fvar :
      {i : Nat}
      {a : 𝔸}
      → -------------
      lc-at i (fvar a)
    lc-at-lam :
      {i : Nat}
      {t : Lam}
      (_ : lc-at (suc i) t)
      → ------------------
      lc-at i (lam t)
    lc-at-app :
      {i : Nat}
      {t t' : Lam}
      (_ : lc-at i t)
      (_ : lc-at i t')
      → -------------------
      lc-at i (app(t , t'))

  -- Local closedness coincides with closed-at-level
  -- (cf. Proposition 4.3)
  fis₁ :
    (i : Nat)
    (t : Lam)
    (p : lc-at i t)
    → -------------
    i ≻ t
  fis₁ i (bvar j) lc-at-bvar k =
    (new Ø , ap var (ifᵈ-≠ (<-not-equal (≤-trans {y = i} auto auto) ∘ sym)))
  fis₁ _ (fvar _) lc-at-fvar _ = (new Ø , refl)
  fis₁ i (lam t) (lc-at-lam p) j  =
    (new Ø , ap lam (≻3 {a = new Ø} (fis₁ (suc i) t p) auto))
  fis₁ i (app (t , t')) (lc-at-app p p') j
    with e ← ≻3 {a = new Ø} (fis₁ i t p) auto
    | e' ← ≻3 {a = new Ø} (fis₁ i t' p') auto
    = (new Ø , ap app (ap₂ _,_ e e'))

  fis₂ :
    (i : Nat)
    (t : Lam)
    (p : i ≻ t)
    → ---------
    lc-at i t
  fis₂ i (bvar j) p = lc-at-bvar ⦃ <-from-not-≤ _ _ ¬i≤j ⦄
    where
    ¬i≤j : ¬ (i ≤ j)
    ¬i≤j i≤j with (_ , q) ← p j ⦃ i≤j ⦄ =
      bvar≠fvar (sym q ∙ ap var (ifᵈ-≡ (refl {x = j})))
  fis₂ _ (fvar _) _ = lc-at-fvar
  fis₂ i (lam t) p = lc-at-lam (fis₂ (suc i) t i+1≻t)
    where
    i+1≻t : suc i ≻ t
    i+1≻t (suc j) ⦃ q ⦄ with (a , e) ← p _ ⦃ ≤-peel q ⦄ = (a , lam-inj e)
  fis₂ i (app(t , t')) p = lc-at-app (fis₂ i t i≻t) (fis₂ i t' i≻t')
    where
    i≻t : i ≻ t
    i≻t j with (a , e) ← p j = (a , fst (app-inj e))
    i≻t' : i ≻ t'
    i≻t' j with (a , e) ← p j = (a , snd (app-inj e))

  -- Bound variables are not locally closed
  ¬0≻bvar : ∀ i → ¬(0 ≻ bvar i)
  ¬0≻bvar i p with fis₂ 0 (bvar i) p
  ... | lc-at-bvar ⦃ () ⦄

  -- Free variables are locally closed
  0≻fvar : ∀ a → 0 ≻ fvar a
  0≻fvar a = fis₁ 0 (fvar a) lc-at-fvar

  -- Local closure of lambda abstractions
  0≻lam : ∀ t → 1 ≻ t → 0 ≻ lam t
  0≻lam t p = fis₁ 0 (lam t) (lc-at-lam (fis₂ 1 t p))

  0≻lam' : ∀ t → 0 ≻ lam t → 1 ≻ t
  0≻lam' t p with fis₂ 0 (lam t) p
  ... | lc-at-lam q = fis₁ 1 t q

  -- Local closure for application terms
  0≻app : ∀ t t' → 0 ≻ t → 0 ≻ t' → 0 ≻ app(t , t')
  0≻app t t' p p' =
    fis₁ 0 (app(t , t')) (lc-at-app (fis₂ 0 t p) (fis₂ 0 t' p'))
  0≻app' : ∀ t t' → 0 ≻ app(t , t') → (0 ≻ t) × (0 ≻ t')
  0≻app' t t' p with fis₂ 0 (app(t , t')) p
  ... | lc-at-app q q' = (fis₁ 0 t q , fis₁ 0 t' q')


  -- Lam is a locally nameless set
  instance
    lnsLam : lns Lam
    ocSet ⦃ lnsLam ⦄ = ocLam
    asupp ⦃ lnsLam ⦄ t = Иi (fv t) λ a ⦃ p ⦄ → fas₁ t a p
    isupp ⦃ lnsLam ⦄ t = (lv t , lv≻ t)
      where
      lv : Lam → Nat
      lv (bvar i)    = suc i
      lv (fvar _)    = 0
      lv (lam t)    = lv t
      lv (app(t , t')) = max (lv t) (lv t')

      lv≻ : (t : Lam) → lv t ≻ t
      lv≻ (bvar i) = fis₁ (suc i) (bvar i) (lc-at-bvar ⦃ ≤-refl ⦄)
      lv≻ (fvar a) = fis₁ 0 (fvar a) lc-at-fvar
      lv≻ (lam t) j with (a , e) ← lv≻ t (suc j) = (a , ap lam e)
      lv≻ (app(t , t')) j
        with (a , e) ← lv≻ t j ⦃ ≤-trans (max-≤l _ _) auto ⦄
        | (a' , e') ← lv≻ t' j ⦃ ≤-trans (max-≤r _ _) auto ⦄ =
        (a , ap₂ (λ x y → app (x , y)) e (≻2 {b = a} e'))

----------------------------------------------------------------------
-- Properties of open/close operations wrt freshness [Lemma 2.12]
----------------------------------------------------------------------
module _
  {X : Type}
  ⦃ _ : oc X ⦄
  {i : Nat}
  {a : 𝔸}
  {A : Finset 𝔸}
  {x : X}
  (f : A atom-supports x)
  where
  ~>atom-supports : A ∪ [ a ] atom-supports (i ~> a)x
  ~>atom-supports b p =
    #1 {i = suc i}{0}
    ((suc i <~ b) ((i ~> a) x) ≡˘⟨ oc₇ i (suc i) a b x ⦃ ¬≡→≠ (<-not-equal auto) ⦄ ⦃ sym≠ b a (∉∷₁ (∉∪₂ A p)) ⦄ ⟩
     (i ~> a) ((suc i <~ b)x)  ≡⟨ ap (i ~> a) (#1 {j = suc i} (f b (∉∪₁ p))) ⟩
     (i ~> a) x                ∎)

  <~atom-supports : A -[ a ] atom-supports (i <~ a)x
  <~atom-supports b p with b ≡? a
  ... | no g =
    (0 <~ b) ((i <~ a) x) ≡⟨ oc₆ 0 i b a x ⦃ ¬≡→≠ g ⦄ ⟩
    (i <~ a) ((0 <~ b)x)  ≡⟨ ap (i <~ a) (f b (minus-∉ p g)) ⟩
    (i <~ a) x            ∎
  ... | yes b≡a = ap (λ b → (0 <~ b)((i <~ a) x)) b≡a ∙ oc₂ 0 i a x

#<~ :
  {X : Type}
  ⦃ _ : oc X ⦄
  (i : Nat)
  (a b : 𝔸)
  (x : X)
  ⦃ _ : a # x ⦄
  → -----------
  a # (i <~ b)x
#<~ i a b x with a ≡? b
... | yes a≡b = ap (λ a → (0 <~ a)((i <~ b) x)) a≡b ∙ oc₂ _ _ _ _
... | no f =
  (0 <~ a) ((i <~ b) x) ≡⟨ oc₆ _ _ _ _ _ ⦃ ¬≡→≠ f ⦄ ⟩
  (i <~ b) ((0 <~ a) x) ≡⟨ ap (i <~ b) (#2 auto) ⟩
  (i <~ b)x             ∎

#~> :
  {X : Type}
  ⦃ _ : oc X ⦄
  (i : Nat)
  (a b : 𝔸)
  (x : X)
  ⦃ _ : a # x ⦄
  ⦃ _ : a ≠ b ⦄
  → -----------
  a # (i ~> b)x
#~> i a b x = #3 {i = suc i}
  ((suc i <~ a)((i ~> b)x) ≡˘⟨ oc₇ _ _ _ _ _ ⦃ ¬≡→≠ (<-not-equal auto) ⦄ ⦃ sym≠ a b auto ⦄ ⟩
   (i ~> b)((suc i <~ a)x) ≡⟨ ap (i ~> b) (#2 auto) ⟩
   (i ~> b)x               ∎)

----------------------------------------------------------------------
-- Properties of open/close operations wrt local closure [Lemma 2.13]
----------------------------------------------------------------------
module _
  {X : Type}
  ⦃ _ : oc X ⦄
  {i : Nat}
  {a : 𝔸}
  {x : X}
  where
  ~>index-supports : -- Equation (10)
    {j : Nat}
    (_ : j ≻ x)
    → -----------
    j ≻ (i ~> a)x
  ~>index-supports p k with k ≡? i
  ... | no f = (a ,
    ((k ~> a)((i ~> a) x) ≡⟨ oc₅ _ _ _ _ _ ⦃ ¬≡→≠ f ⦄ ⟩
     (i ~> a)((k ~> a) x) ≡⟨ ap (i ~> a) (≻3 p auto) ⟩
     (i ~> a) x           ∎))
  ... | yes k≡i = (a , ap (λ k → (k ~> a)((i ~> a) x)) k≡i ∙ oc₁ _ _ _ _)

  ~>index-supports' : -- Equation (11)
    suc i ≻ x → i ≻ (i ~> a) x
  ~>index-supports' p j with j ≡? i
  ... | no f = (a ,
    ((j ~> a)((i ~> a) x)  ≡⟨ oc₅ _ _ _ _ _ ⦃ ¬≡→≠ f ⦄ ⟩
     (i ~> a) ((j ~> a) x) ≡⟨ ap (i ~> a) (≻3 p (<-from-≤ (f ∘ sym) auto)) ⟩
     (i ~> a) x            ∎))
  ... | yes j≡i = (a , ap (λ j → (j ~> a)((i ~> a) x)) j≡i ∙ oc₁ _ _ _ _)

  <~index-supports : -- Equation (12)
    {j : Nat}
    (_ : j ≻ x)
    → ------------------------
    max j (suc i) ≻ (i <~ a) x
  <~index-supports p k with (b , q) ← fresh{𝔸} [ a ] =
    (b ,
      ((k ~> b)((i <~ a) x) ≡⟨ oc₇ _ _ _ _ _ ⦃ i≠k ⦄ ⦃ ∉∷₁ q ⦄ ⟩
       (i <~ a)((k ~> b) x) ≡⟨ ap (i <~ a) (≻3 p (≤-trans (max-≤l _ _) auto)) ⟩
       (i <~ a) x           ∎))
    where i≠k = ¬≡→≠ (<-not-equal (≤-trans (max-≤r _ _) auto) ∘ sym)
