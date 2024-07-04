module Lib.Support where

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.Freshness
open import Lib.LocalClosedness

----------------------------------------------------------------------
-- Locally nameless sets [Definition 2.9]
----------------------------------------------------------------------
record lns (X : Set) : Set where
  constructor mklns
  field
    {{ocSet}} : oc X
    asupp : (x : X) → И a ∶ 𝔸 , a # x
    isupp : (x : X) → ∑ i ∶ ℕ , i ≻ x

open lns{{...}} public

infix 4 _atom-supports_
_atom-supports_ :
  {X : Set}
  {{_ : oc X}}
  (A : Fset 𝔸)
  (x : X)
  → ----------
  Set
A atom-supports x = ∀ a → a ∉ A → a # x

----------------------------------------------------------------------
-- Locally nameless set of indices and atoms [Example 2.10]
----------------------------------------------------------------------
lnsℕ𝔸 : lns ℕ𝔸
ocSet {{lnsℕ𝔸}} = ocℕ𝔸
asupp {{lnsℕ𝔸}} (ι₁ i) = Иi Ø λ _ → refl
asupp {{lnsℕ𝔸}} (ι₂ a) = Иi [ a ] и₂
  where
  и₂ : (b : 𝔸){{_ : b ∉ [ a ]}} → b # ι₂ a
  и₂ b {{∉[]{{p}}}} rewrite p = refl
isupp {{lnsℕ𝔸}} (ι₁ i) = (i +1 , s₂)
  where
  s₂ : i +1 ≻ ι₁ i
  s₂ j {{p}} rewrite +1≤→≠ i j p = (new Ø , refl)
isupp {{lnsℕ𝔸}} (ι₂ a) = (0 , λ _ → (a , refl))

----------------------------------------------------------------------
-- Lambda terms [Example 2.11]
----------------------------------------------------------------------
module LambdaTerm where
  data Lam : Set where
    var : ℕ𝔸 → Lam
    lam : Lam → Lam
    app : Lam × Lam → Lam

  pattern bvar i = var (ι₁ i)
  pattern fvar a = var (ι₂ a)

  lam-inj : ∀{t t'} → lam t ≡ lam t' → t ≡ t'
  lam-inj refl = refl

  app-inj :
    {t₁ t₂ t₁' t₂' : Lam}
    (_ : app(t₁ , t₂) ≡ app(t₁' , t₂'))
    → ---------------------------------
    (t₁ ≡ t₁') × (t₂ ≡ t₂')
  app-inj refl = refl , refl

  -- Lam is an oc-set
  instance
    ocLam : oc Lam
    ocLam = mkoc opn cls ax₁ ax₂ ax₃ ax₄ ax₅ ax₆ ax₇ ax₈ ax₉
      where
      X = Lam
      opn : ℕ → 𝔸 → X → X
      opn i a (var v)   = var ((i ~> a) v)
      opn i a (lam t) = lam(opn (i +1) a t)
      opn i a (app(t , t')) = app(opn i a t , opn i a t')
      cls : ℕ → 𝔸 → X → X
      cls i a (var v)   = var ((i <~ a) v)
      cls i a (lam t) = lam(cls (i +1) a t)
      cls i a (app(t , t')) = app(cls i a t , cls i a t')
      ax₁ :
        (i : ℕ)
        (a b : 𝔸)
        (t : X)
        → -----------------------------
        opn i a (opn i b t) ≡ opn i b t
      ax₁ i a b (var v)
        rewrite oc₁ i a b v = refl
      ax₁ i a b (lam t)
        rewrite ax₁ (1 + i) a b t = refl
      ax₁ i a b (app(t , t'))
        rewrite ax₁ i a b t | ax₁ i a b t' = refl
      ax₂ :
        (i j : ℕ)
        (a : 𝔸)
        (t : X)
        → -----------------------------
        cls i a (cls j a t) ≡ cls j a t
      ax₂ i j a (var v)
        rewrite oc₂ i j a v = refl
      ax₂ i j a (lam t)
        rewrite ax₂ (1 + i) (j +1) a t = refl
      ax₂ i j a (app(t , t'))
        rewrite ax₂ i j a t | ax₂ i j a t' =  refl
      ax₃ :
        (i : ℕ)
        (a : 𝔸)
        (t : X)
        → -----------------------------
        cls i a (opn i a t) ≡ cls i a t
      ax₃ i a (var v)
        rewrite oc₃ i a v = refl
      ax₃ i a (lam t)
        rewrite ax₃ (1 + i) a t = refl
      ax₃ i a (app(t , t'))
        rewrite ax₃ i a t | ax₃ i a t' = refl
      ax₄ :
        (i : ℕ)
        (a : 𝔸)
        (t : X)
        → -----------------------------
          opn i a (cls i a t) ≡ opn i a t
      ax₄ i a (var v)
        rewrite oc₄ i a v = refl
      ax₄ i a (lam t)
        rewrite ax₄ (1 + i) a t = refl
      ax₄ i a (app(t , t'))
        rewrite ax₄ i a t | ax₄ i a t' = refl
      ax₅ :
        (i j : ℕ)
        (a b : 𝔸)
        (t : X)
        {{_ : i ≠ j}}
        → ---------------------------------------
        opn i a (opn j b t) ≡ opn j b (opn i a t)
      ax₅ i j a b (var v)
        rewrite oc₅ i j a b v {{it}} = refl
      ax₅ i j a b (lam t)
        rewrite ax₅ (i +1) (j +1) a b t {{+1≠ {i} it}} = refl
      ax₅ i j a b  (app(t , t'))
        rewrite ax₅ i j a b t {{it}} | ax₅ i j a b t' {{it}} = refl
      ax₆ :
        (i j : ℕ)
        (a b : 𝔸)
        (t : X)
          {{_ : a ≠ b}}
        → ---------------------------------------
        cls i a (cls j b t) ≡ cls j b (cls i a t)
      ax₆ i j a b (var v)
        rewrite oc₆ i j a b v {{it}} = refl
      ax₆ i j a b (lam t)
        rewrite ax₆ (i +1) (j +1) a b t {{it}} = refl
      ax₆ i j a b (app(t , t'))
        rewrite ax₆ i j a b t {{it}} | ax₆ i j a b t' {{it}} = refl
      ax₇ :
        (i j : ℕ)
        (a b : 𝔸)
        (t : X)
        {{_ : i ≠ j}}
        {{_ : a ≠ b}}
        → ---------------------------------------
          opn i a (cls j b t) ≡ cls j b (opn i a t)
      ax₇ i j a b (var v)
        rewrite oc₇ i j a b v {{it}} {{it}} = refl
      ax₇ i j a b (lam t)
        rewrite ax₇ (i +1) (j +1) a b t {{+1≠ {i} it}} {{it}} = refl
      ax₇ i j a b (app(t , t'))
        rewrite ax₇ i j a b t {{it}} {{it}}
        | ax₇ i j a b t' {{it}} {{it}} = refl
      ax₈ :
        (i j : ℕ)
        (a b : 𝔸)
        (t : X)
        → -----------------------------------------------------------
        opn i b (cls i a (opn j b t)) ≡ opn j b (cls j a (opn i a t))
      ax₈ i j a b (var v)
        rewrite oc₈ i j a b v = refl
      ax₈ i j a b (lam t)
        rewrite ax₈ (i +1) (j +1) a b t = refl
      ax₈ i j a b  (app(t , t'))
        rewrite ax₈ i j a b t | ax₈ i j a b t' = refl
      ax₉ :
        (i j : ℕ)
        (a b : 𝔸)
        (t : X)
        → -----------------------------------------------------------
        cls j a (opn i a (cls j b t)) ≡ cls j b (opn i b (cls i a t))
      ax₉ i j a b (var v)
        rewrite oc₉ i j a b v = refl
      ax₉ i j a b (lam t)
        rewrite ax₉ (i +1) (j +1) a b t = refl
      ax₉ i j a b (app(t , t'))
        rewrite ax₉ i j a b t | ax₉ i j a b t' = refl


  -- Free variables deined inductively
  fv : Lam → Fset 𝔸
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
  fas₁ (fvar b) a _          with  a ≐ b
  fas₁ (fvar _) _ _          | neq _ = refl
  fas₁ (fvar b) _ (∉[]{{p}}) | equ with () ← ¬≠ b p
  fas₁ (lam t) a p = ap lam p'
    where
    p' : (1 <~ a)t ≡ t
    p' =
      proof
        (1 <~ a)t
      [ ap (1 <~ a) (fas₁ t a p) ]≡
      (1 <~ a)((0 <~ a)t)
      ≡[ oc₂ 1 0 a t ]
        (0 <~ a)t
      ≡[ fas₁ t a p ]
        t
      qed
  fas₁ (app(t , t')) a (∉∪{{p}}{{p'}})
    rewrite fas₁ t a p | fas₁ t' a p' = refl

  fas₂ :
    (t : Lam)
    (a : 𝔸)
    (_ : a # t)
    → ---------
    a ∉ fv t
  fas₂ (bvar _) _ _ = ∉Ø
  fas₂ (fvar b) a p  with a ≐ b in eq
  fas₂ (fvar b) a _  | neq f = ∉[] {x = a} {b} {{dec-neq a b f}}
  fas₂ (fvar _) _ () | equ
  fas₂ (lam t) a p = fas₂ t a p'
    where
    p' : (0 <~ a)t ≡ t
    p' =
      proof
        (0 <~ a)t
      [ ap (0 <~ a) (lam-inj p) ]≡
        (0 <~ a)((1 <~ a)t)
      ≡[ oc₂ 0 1 a t ]
        (1 <~ a)t
      ≡[ lam-inj p ]
        t
      qed
  fas₂ (app(t , t')) a p = ∉∪ {xs = fv t} {fv t'}
    {{fas₂ t  a (π₁ (app-inj p))}}
    {{fas₂ t' a (π₂ (app-inj p))}}

  -- Inductive closed-at-level predicate
  data lc-at : ℕ → Lam → Set where
    lc-at-bvar :
      {i j : ℕ}
      {{_ : j < i}}
      → --------------
      lc-at i (bvar j)
    lc-at-fvar :
      {i : ℕ}
      {a : 𝔸}
      → -------------
      lc-at i (fvar a)
    lc-at-lam :
      {i : ℕ}
      {t : Lam}
      (_ : lc-at (i +1) t)
      → ------------------
      lc-at i (lam t)
    lc-at-app :
      {i : ℕ}
      {t t' : Lam}
      (_ : lc-at i t)
      (_ : lc-at i t')
      → -------------------
      lc-at i (app(t , t'))

  -- Local closedness coincides with closed-at-level
  -- (cf. Proposition 4.3)
  fis₁ :
    (i : ℕ)
    (t : Lam)
    (p : lc-at i t)
    → -------------
    i ≻ t
  fis₁ i (bvar j) lc-at-bvar k
    rewrite <→≠ j k (<≤ it it) = (new Ø , refl)
  fis₁ _ (fvar _) lc-at-fvar _ = (new Ø , refl)
  fis₁ i (lam t) (lc-at-lam p) j  =
    (new Ø , ap lam (≻3 {a = new Ø} (fis₁ (i +1) t p) (+1≤ it)))
  fis₁ i (app (t , t')) (lc-at-app p p') j
    with e ← ≻3 {a = new Ø} (fis₁ i t p) it
    | e' ← ≻3 {a = new Ø} (fis₁ i t' p') it
    = (new Ø , ap₂ (λ x y → app (x , y)) e e')

  fis₂ :
    (i : ℕ)
    (t : Lam)
    (p : i ≻ t)
    → ---------
    lc-at i t
  fis₂ i (bvar j) p = lc-at-bvar{{trich' ¬i≤j}}
    where
    ¬i≤j : ¬ (i ≤ j)
    ¬i≤j i≤j
      with (_ , q) ← p j {{i≤j}}
      rewrite dec-equ j
      with () ← q
  fis₂ _ (fvar _) _ = lc-at-fvar
  fis₂ i (lam t) p = lc-at-lam (fis₂ (i +1) t i+1≻t)
    where
    i+1≻t : i +1 ≻ t
    i+1≻t _ ⦃ +1≤ ev ⦄
      with (a , e) ←  p _  {{ev}} = (a , lam-inj e)
  fis₂ i (app(t , t')) p = lc-at-app (fis₂ i t i≻t) (fis₂ i t' i≻t')
    where
    i≻t : i ≻ t
    i≻t j {{q}} with (a , e) ← p j {{q}} = (a , π₁ (app-inj e))
    i≻t' : i ≻ t'
    i≻t' j {{q}} with (a , e) ← p j {{q}} = (a , π₂ (app-inj e))

  -- Boundvariables are not locally closed
  ¬0≻bvar : ∀ i → ¬(0 ≻ bvar i)
  ¬0≻bvar i p with fis₂ 0 (bvar i) p
  ... | lc-at-bvar {{q}} with () ← q

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
    ocSet {{lnsLam}} = ocLam
    asupp {{lnsLam}} t = Иi (fv t) λ a {{p}} → fas₁ t a p
    isupp {{lnsLam}} t = (lv t , lv≻ t)
      where
      lv : Lam → ℕ
      lv (bvar i)    = i +1
      lv (fvar _)    = 0
      lv (lam t)    = lv t
      lv (app(t , t')) = max (lv t) (lv t')

      lv≻ : (t : Lam) → lv t ≻ t
      lv≻ (bvar i) = fis₁ (i +1) (bvar i) (lc-at-bvar{{≤refl}})
      lv≻ (fvar a) = fis₁ 0 (fvar a) lc-at-fvar
      lv≻ (lam t) j with (a , e) ← lv≻ t (j +1) {{≤+1 it}} = (a , ap lam e)
      lv≻ (app(t , t')) j
        with (a , e) ← lv≻ t j {{≤trans ≤max₁ it}}
        | (a' , e') ← lv≻ t' j {{≤trans ≤max₂ it}} =
        (a , ap₂ (λ x y → app (x , y)) e (≻2 {b = a} e'))

----------------------------------------------------------------------
-- Properties of open/close operations wrt freshness [Lemma 2.12]
----------------------------------------------------------------------
module _
  {X : Set}
  {{_ : oc X}}
  {i : ℕ}
  {a : 𝔸}
  {A : Fset 𝔸}
  {x : X}
  (f : A atom-supports x)
  where
  ~>atom-supports : A ∪ [ a ] atom-supports (i ~> a)x
  ~>atom-supports b (∉∪{{_}}{{∉[]}}) =
    #1 {i = i +1}{0}
    (proof
       ((i +1) <~ b) ((i ~> a) x)
     [ oc₇ i (i +1) a b x {{ ≠+1 i}} {{symm≠ b a it}} ]≡
       (i ~> a) ((i +1 <~ b)x)
     ≡[ ap (i ~> a) (#1 {j = i +1} (f b it)) ]
       (i ~> a) x
     qed)

  <~atom-supports : A -[ a ] atom-supports (i <~ a)x
  <~atom-supports b p with b ≐ a
  ... | neq g =
    proof
      (0 <~ b) ((i <~ a) x)
    ≡[ oc₆ 0 i b a x {{¬≡→≠ g}} ]
      (i <~ a) ((0 <~ b)x)
    ≡[ ap (i <~ a) (f b (∉-[] p (¬≡→≠ g))) ]
      (i <~ a) x
    qed
  ... | equ = oc₂ 0 i b x

#<~ :
  {X : Set}
  {{_ : oc X}}
  (i : ℕ)
  (a b : 𝔸)
  (x : X)
  {{_ : a # x}}
  → -----------
  a # (i <~ b)x
#<~ i a b x with a ≐ b
... | equ = oc₂ _ _ _ _
... | neq f =
  proof
    (0 <~ a) ((i <~ b) x)
  ≡[ oc₆ _ _ _ _ _ {{¬≡→≠ f}} ]
    (i <~ b) ((0 <~ a) x)
  ≡[ ap (i <~ b) (#2 it) ]
    (i <~ b)x
  qed

#~> :
  {X : Set}
  {{_ : oc X}}
  (i : ℕ)
  (a b : 𝔸)
  (x : X)
  {{_ : a # x}}
  {{_ : a ≠ b}}
  → -----------
  a # (i ~> b)x
#~> i a b x = #3 {i = i +1}
  (proof
     (i +1 <~ a)((i ~> b)x)
   [ oc₇ _ _ _ _ _ {{≠+1 i}}{{symm≠ a b it}} ]≡
     (i ~> b)((i +1 <~ a)x)
   ≡[ ap (i ~> b) (#2 it) ]
     (i ~> b)x
   qed)

----------------------------------------------------------------------
-- Properties of open/close operations wrt local closure [Lemma 2.13]
----------------------------------------------------------------------
module _
  {X : Set}
  {{_ : oc X}}
  {i : ℕ}
  {a : 𝔸}
  {x : X}
  where
  ~>index-supports : -- Equation (10)
    {j : ℕ}
    (_ : j ≻ x)
    → -----------
    j ≻ (i ~> a)x
  ~>index-supports p k with k ≐ i
  ... | neq f = (a ,
    (proof
       (k ~> a)((i ~> a) x)
     ≡[ oc₅ _ _ _ _ _ {{¬≡→≠ f}} ]
       (i ~> a)((k ~> a) x)
     ≡[ ap (i ~> a) (≻3 p it) ]
       (i ~> a) x
     qed))
  ... | equ = (a , oc₁ _ _ _ _)

  ~>index-supports' : -- Equation (11)
    i +1 ≻ x → i ≻ (i ~> a) x
  ~>index-supports' p j with j ≐ i
  ... | neq f = (a ,
    (proof
       (j ~> a)((i ~> a) x)
     ≡[ oc₅ _ _ _ _ _ {{¬≡→≠ f}}  ]
       (i ~> a) ((j ~> a) x)
     ≡[ ap (i ~> a) (≻3 p (≤≠ it (symm≠ j i (¬≡→≠ f)))) ]
       (i ~> a) x
     qed))
  ... | equ = (a , oc₁ _ _ _ _)

  <~index-supports : -- Equation (12)
    {j : ℕ}
    (_ : j ≻ x)
    → ------------------------
    max j (i +1) ≻ (i <~ a) x
  <~index-supports p k with (b , ∉[]) ← fresh{𝔸} [ a ] =
    (b ,
      (proof
        (k ~> b)((i <~ a) x)
      ≡[ oc₇ _ _ _ _ _ {{+1≤→≠ i k (≤trans ≤max₂ it)}} ]
        (i <~ a)((k ~> b) x)
      ≡[ ap (i <~ a) (≻3 p (≤trans ≤max₁ it)) ]
        (i <~ a) x
      qed))
