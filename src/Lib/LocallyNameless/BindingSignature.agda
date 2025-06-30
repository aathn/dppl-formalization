--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.LocallyNameless.BindingSignature where

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets
open import Lib.LocallyNameless.Freshness
open import Lib.LocallyNameless.LocalClosedness
open import Lib.LocallyNameless.Support
open import Lib.LocallyNameless.AbstractionConcretion
open import Lib.LocallyNameless.RenamingReindexingSwapping
open import Lib.LocallyNameless.Category
open import Lib.LocallyNameless.Shift
open import Lib.FunExt

----------------------------------------------------------------------
-- Plotkin's binding signatures [Section 4.1]
----------------------------------------------------------------------
record Sig : Set₁ where
  constructor mkSig
  field
    Op : Set
    ar : Op → Array ℕ

open Sig public

-- Example: the binding signature for untyped λ-terms
ΛSig : Sig
ΛSig = mkSig ΛOp ΛAr
  module _ where
    data ΛOp : Set where
      Λlam : ΛOp
      Λapp : ΛOp
    ΛAr : ΛOp → Array ℕ
    length (ΛAr Λlam)             = 1 -- lam is unary
    index  (ΛAr Λlam) zero        = 1 -- and binds one variable
    length (ΛAr Λapp)             = 2 -- app is binary
    index  (ΛAr Λapp) zero        = 0 -- and binds no variables...
    index  (ΛAr Λapp) (succ zero) = 0 -- ...in each argument

----------------------------------------------------------------------
-- Set functor associated with a signature
----------------------------------------------------------------------
infixr 8 _∙_ _∙′_
_∙_ : Sig → Set → Set
Σ ∙ X  = ∑ c ∶ Op Σ , (Fin (length (ar Σ c)) → X) -- Equation (58)

_∙′_ : (Σ : Sig){X Y : Set} → (X → Y) → Σ ∙ X → Σ ∙ Y
(Σ ∙′ f) (c , t) = (c , (f ∘ t))

-- Action of Σ ∙_ on locally nameless sets
instance
  oc∙ :
    {Σ : Sig}
    {X : Set}
    {{_ : oc X}}
    → ----------
    oc (Σ ∙ X)
  _~>_ {{oc∙{Σ}}} i a (c , t) =
    (c , λ k → (i + index (ar Σ c) k ~> a)(t k))
  _<~_ {{oc∙{Σ}}} i a (c , t) =
    (c , λ k → (i + index (ar Σ c) k <~ a)(t k))
  oc₁ {{oc∙{Σ}}} i a b (c , t) = ap (c ,_) (funext λ k →
    oc₁ (i + index (ar Σ c) k) a b (t k))
  oc₂ {{oc∙{Σ}}} i j a (c , t) = ap (c ,_) (funext λ k →
    oc₂ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a (t k))
  oc₃ {{oc∙{Σ}}} i a (c , t) = ap (c ,_) (funext λ k →
    oc₃ (i + index (ar Σ c) k) a (t k))
  oc₄ {{oc∙{Σ}}} i a (c , t) = ap (c ,_) (funext λ k →
    oc₄ (i + index (ar Σ c) k) a (t k))
  oc₅ {{oc∙{Σ}}} i j a b (c , t) = ap (c ,_) (funext λ k →
    oc₅ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a  b (t k)
    {{+≠ {x = i} (index (ar Σ c) k) it}})
  oc₆ {{oc∙{Σ}}} i j a b (c , t) = ap (c ,_) (funext λ k →
    oc₆ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a  b (t k))
  oc₇ {{oc∙{Σ}}} i  j a b (c , t) = ap (c ,_) (funext λ k →
    oc₇ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a  b (t k)
    {{+≠ {x = i} (index (ar Σ c) k) it}})
  oc₈ {{oc∙{Σ}}} i j a b (c , t) = ap (c ,_) (funext λ k →
    oc₈ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a  b (t k))
  oc₉ {{oc∙{Σ}}} i j a b (c , t) = ap (c ,_) (funext λ k →
    oc₉ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a  b (t k))

#oc∙ :
  {Σ : Sig}
  {X : Set}
  {{_ : oc X}}
  {c : Op Σ}
  {f : Fin (length (ar Σ c)) → X}
  (a : 𝔸)
  (_ : ∀ k → a # f k)
  → ----------------------------
  _#_ {{oc∙{Σ}}} a (c , f)
#oc∙ {Σ} a g = ap (_ ,_) (funext λ k → #1 (g k))

≻oc∙ :
  {Σ : Sig}
  {X : Set}
  {{_ : oc X}}
  {c : Op Σ}
  {f : Fin (length (ar Σ c)) → X}
  (i : ℕ)
  (_ : ∀ k → i + index (ar Σ c) k ≻ f k)
  → ------------------------------------
  _≻_ {{oc∙{Σ}}} i (c , f)
≻oc∙ {Σ} i g j =
  (new Ø , ap (_ ,_) (funext λ k → ≻3 (g k) (+≤ _ it)))

instance
  lns∙ :
    {Σ : Sig}
    {X : Set}
    {{_ : lns X}}
    → -----------
    lns (Σ ∙ X)
  ocSet {{lns∙{Σ}}} = oc∙{Σ}
  asupp {{lns∙{Σ}}} (c , f) = Иi
    (⋃ λ k →  Иe₁ (asupp (f k)))
    λ a → #oc∙ {Σ} a λ k → Иe₂ (asupp (f k)) a {{∉⋃ _ k}}
  isupp {{lns∙{Σ}}} (c , f) =
    let i = Max λ k →  π₁ (isupp (f k)) in
    (i , ≻oc∙ {Σ} i λ k →  ≻1 (≤+ _ (≤Max _ k)) (π₂ (isupp (f k))))

-- Action of Σ ∙′_ on morphisms of locally nameless sets
instance
  oc∙′ :
    {Σ : Sig}
    {X Y : Set}
    {{ocX : oc X}}
    {{ocY : oc Y}}
    {φ : X → Y}
    {{_ : oc-hom φ}}
    → -----------------------------------
    oc-hom {{oc∙{Σ}}} {{oc∙{Σ}}} (Σ ∙′ φ)
  oc-hom-open {{oc∙′}} (c , _) =
    ap (c ,_) (funext λ _ → oc-hom-open _)
  oc-hom-close {{oc∙′}} (c , _) =
    ap (c ,_) (funext λ _ → oc-hom-close _)

  lns∙′ :
    {Σ : Sig}
    {X Y : Set}
    {{lnsX : lns X}}
    {{lnsY : lns Y}}
    {φ : X → Y}
    {{_ : lns-hom φ}}
    → --------------------------------------
    lns-hom {{lns∙{Σ}}} {{lns∙{Σ}}} (Σ ∙′ φ)
  ochom {{lns∙′}} = oc∙′

----------------------------------------------------------------------
-- Terms over a binding signature [Equation (65)]
----------------------------------------------------------------------
data Trm (Σ : Sig) : Set where
  var : ℕ𝔸 → Trm Σ
  op  : Σ ∙ Trm Σ → Trm Σ

pattern bvar i = var (ι₁ i)
pattern fvar a = var (ι₂ a)

op-injective :
  {Σ : Sig}
  {c c' : Op Σ}
  {ts  : Fin (length (ar Σ c))  → Trm Σ}
  {ts' : Fin (length (ar Σ c')) → Trm Σ}
  (_ : op(c , ts) ≡ op(c' , ts'))
  → ------------------------------------
  ∑ H≡ ∶ c ≡ c' , subst _ H≡ ts ≡ ts'
op-injective refl = refl , refl

op-inj :
  {Σ : Sig}
  {c : Op Σ}
  {ts ts' : Fin (length (ar Σ c)) → Trm Σ}
  (_ : op(c , ts) ≡ op(c , ts'))
  (k : Fin (length (ar Σ c)))
  → --------------------------------------
  ts k ≡ ts' k
op-inj refl _ = refl

----------------------------------------------------------------------
-- The terms form a locally nameless set
----------------------------------------------------------------------
-- The oc-Set structure
instance
  ocTrm : {Σ : Sig} → oc (Trm Σ)
  ocTrm {Σ} = mkoc opn cls ax₁ ax₂ ax₃ ax₄ ax₅ ax₆ ax₇ ax₈ ax₉
    where
    X = Trm Σ
    opn : ℕ → 𝔸 → X → X
    opn i a (var v)   = var ((i ~> a) v)
    opn i a (op(c , ts)) =
      op(c , λ k → opn (i + index (ar Σ c) k) a (ts k))
    cls : ℕ → 𝔸 → X → X
    cls i a (var v)   = var ((i <~ a) v)
    cls i a (op(c , ts)) =
      op(c , λ k → cls (i + index (ar Σ c) k) a (ts k))
    ax₁ :
      (i : ℕ)
      (a b : 𝔸)
      (t : Trm Σ)
      → -----------------------------
      opn i a (opn i b t) ≡ opn i b t
    ax₁ i a b (var v) rewrite oc₁ i a b v = refl
    ax₁ i a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₁ (i + index (ar Σ c) k) a b (ts k))
    ax₂ :
      (i j : ℕ)
      (a : 𝔸)
      (t : Trm Σ)
      → -----------------------------
      cls i a (cls j a t) ≡ cls j a t
    ax₂ i j a (var v) rewrite oc₂ i j a v = refl
    ax₂ i j a (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₂ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a (ts k))
    ax₃ :
      (i : ℕ)
      (a : 𝔸)
      (t : Trm Σ)
      → -----------------------------
      cls i a (opn i a t) ≡ cls i a t
    ax₃ i a (var v) rewrite oc₃ i a v = refl
    ax₃ i a (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₃ (i + index (ar Σ c) k) a (ts k))
    ax₄ :
      (i : ℕ)
      (a : 𝔸)
      (t : Trm Σ)
      → -----------------------------
      opn i a (cls i a t) ≡ opn i a t
    ax₄ i a (var v) rewrite oc₄ i a v = refl
    ax₄ i a (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₄ (i + index (ar Σ c) k) a (ts k))
    ax₅ :
      (i j : ℕ)
      (a b : 𝔸)
      (t : Trm Σ)
      {{_ : i ≠ j}}
      → ---------------------------------------
      opn i a (opn j b t) ≡ opn j b (opn i a t)
    ax₅ i j a b (var v) rewrite oc₅ i j a b v {{it}} = refl
    ax₅ i j a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₅ (i + index (ar Σ c) k)
          (j + index (ar Σ c) k) a b (ts k)
          {{+≠ {x = i} (index (ar Σ c) k) it}})
    ax₆ :
      (i j : ℕ)
      (a b : 𝔸)
      (t : Trm Σ)
      {{_ : a ≠ b}}
      → ---------------------------------------
      cls i a (cls j b t) ≡ cls j b (cls i a t)
    ax₆ i j a b (var v) rewrite oc₆ i j a b v {{it}} = refl
    ax₆ i j a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₆ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a b (ts k))
    ax₇ :
      (i j : ℕ)
      (a b : 𝔸)
      (t : Trm Σ)
      {{_ : i ≠ j}}
      {{_ : a ≠ b}}
      → ---------------------------------------
      opn i a (cls j b t) ≡ cls j b (opn i a t)
    ax₇ i j a b (var v) rewrite oc₇ i j a b v {{it}} {{it}} = refl
    ax₇ i j a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₇ (i + index (ar Σ c) k)
          (j + index (ar Σ c) k) a b (ts k)
          {{+≠ {x = i} (index (ar Σ c) k) it}})
    ax₈ :
      (i j : ℕ)
      (a b : 𝔸)
      (t : Trm Σ)
      → -----------------------------------------------------------
      opn i b (cls i a (opn j b t)) ≡ opn j b (cls j a (opn i a t))
    ax₈ i j a b (var v) rewrite oc₈ i j a b v = refl
    ax₈ i j a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₈ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a b (ts k))
    ax₉ :
      (i j : ℕ)
      (a b : 𝔸)
      (t : Trm Σ)
      → -----------------------------------------------------------
      cls j a (opn i a (cls j b t)) ≡ cls j b (opn i b (cls i a t))
    ax₉ i j a b (var v) rewrite oc₉ i j a b v = refl
    ax₉ i j a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₉ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a b (ts k))

-- A lemma about atom-support in Trm Σ
#Trm :
  {Σ : Sig}
  (c : Op Σ)
  (ts : Fin (length (ar Σ c)) → Trm Σ)
  (a : 𝔸)
  (_ : ∀ k → a # ts k)
  → ----------------------------------
   a # op(c , ts)
#Trm {Σ} c ts a f = ap (λ ts' → op(c , ts')) (funext λ k → #1 (f k))

-- Lemmas about index-support in Trm Σ
≻Trm :
  {Σ : Sig}
  (c : Op Σ)
  (ts : Fin (length (ar Σ c)) → Trm Σ)
  (i : ℕ)
  (_ : ∀ k → i + index (ar Σ c) k ≻ ts k)
  → -------------------------------------
  i ≻ op(c , ts)
≻Trm {Σ} c ts i f j = (new Ø , ap (λ ts' →
  op(c , ts')) (funext λ k → ≻3 (f k) (+≤ _ it)))

≻Trm′ :
  {Σ : Sig}
  (c : Op Σ)
  (ts : Fin (length (ar Σ c)) → Trm Σ)
  (i : ℕ)
  (_ : i ≻ op(c , ts))
  (k : Fin (length (ar Σ c)))
  → ----------------------------------
  i + index (ar Σ c) k ≻ ts k
≻Trm′ {Σ} c ts i p k j
  with (a , q) ← p (j ∸ index (ar Σ c) k) {{∸adj it}} = (a , e')
  where
  e' : (j ~> a)(ts k) ≡ ts k
  e' =
    proof
      (j ~> a)(ts k)
    [ ap (λ j' → (j' ~> a)(ts k))
      (∸≤' {j} {index (ar Σ c) k}  (≤trans (≤+' _ ≤refl) it)) ]≡
      ((j ∸ index (ar Σ c) k + index (ar Σ c) k) ~> a)(ts k)
    ≡[ op-inj q k ]
      ts k
    qed

-- The finite support properties
lnsTrm : {Σ : Sig} → lns (Trm Σ)
lnsTrm {Σ} = mklns asp isp
  where
  instance
    _ : lns ℕ𝔸
    _ = lnsℕ𝔸
  asp : (t : Trm Σ) → И a ∶ 𝔸 , a # t
  asp (var v) with Иi и₁ и₂ ← asupp v =
    Иi и₁ (λ a → ap var (и₂ a))
  asp (op(c , ts)) = Иi
    (⋃ λ k →  Иe₁ (asp (ts k)))
    (λ a → #Trm c ts a λ k → Иe₂ (asp (ts k)) a {{∉⋃ _ k}})
  isp : (t : Trm Σ) → ∑ i ∶ ℕ , i ≻ t
  isp (var v) with (i , p) ← isupp v =
    (i , λ j → (π₁ (p j)) , ap var (π₂ (p j)))
  isp (op(c , ts)) =
    let i = Max λ k →  π₁ (isp (ts k)) in
    (i ,  ≻Trm c ts i λ k → ≻1 (≤+ _ (≤Max _ k)) (π₂ (isp (ts k))) )

----------------------------------------------------------------------
-- The locally nameless set Trm Σ is the free Σ∙_-algebra on ℕ𝔸
-- [Theorem 4.1]
----------------------------------------------------------------------
module UniversalProperty
  {- We can prove the universal property with respect to all oc-sets
     X, rather than just locally nameless ones. -}
  {Σ : Sig}
  {X : Set}
  (f : ℕ𝔸 → X)
  (g : Σ ∙ X → X)
  where
  instance
    _ : lns ℕ𝔸
    _ = lnsℕ𝔸
    _ : lns (Trm Σ)
    _ = lnsTrm
  -- Existence
  rec : Trm Σ → X
  rec (var v)      = f v
  rec (op(c , ts)) = g (c , λ k → rec (ts k))
  -- Uniqueness [Equation (61)]
  module _
    (h : Trm Σ → X)
    (hvar : ∀ v → h (var v) ≡ f v)
    (hop : ∀ x → h(op x) ≡ g ((Σ ∙′ h) x))
    where
    uniq : h ≡ rec
    uniq = funext uniq'
      where
      uniq' : ∀ t → h t ≡ rec t
      uniq' (var v) = hvar v
      uniq' (op(c , ts)) =
        proof
          h (op (c , ts))
        ≡[ hop (c , ts) ]
          g ((Σ ∙′ h)(c , ts))
        ≡[]
          g (c , (h ∘ ts))
        ≡[ ap (λ x → g (c , x)) (funext λ k → uniq' (ts k)) ]
          g (c , λ k → rec (ts k))
        qed

    -- If we assume X is also an oc-set and that
    -- f, g and h are morphisms of oc-sets...
    module _
      {{_ : oc X}}
      {{homf : oc-hom f}}
      {{homg : oc-hom {{oc∙{Σ}}} g}}
      {{_ : oc-hom h}}
      where
    -- ...then rec is also a morphism
        rec-hom : oc-hom rec
        rec-hom = mkoc-hom hopn hcls
          where
          hopn :
            {i : ℕ}
            {a : 𝔸}
            (t : Trm Σ)
            → --------------------------------
            rec ((i ~> a)t) ≡ (i ~> a) (rec t)
          hopn (var v) = oc-hom-open v
          hopn {i} {a} (op(c , ts)) =
            proof
              g (c , λ k → rec ((i + index (ar Σ c) k ~> a)(ts k)))
            ≡[ ap (λ t → g(c , t)) (funext λ k →
              hopn {i + index (ar Σ c) k} {a} (ts k))]
              g (_~>_ {{oc∙{Σ}}} i a (c , λ k → rec (ts k)))
            ≡[ oc-hom-open _ ]
              (i ~> a) (g (c , λ k → rec (ts k)))
            qed
          hcls :
            {i : ℕ}
            {a : 𝔸}
            (t : Trm Σ)
            → --------------------------------
            rec ((i <~ a)t) ≡ (i <~ a) (rec t)
          hcls (var v) = oc-hom-close v
          hcls {i} {a} (op(c , ts)) =
            proof
              g (c , λ k → rec ((i + index (ar Σ c) k <~ a)(ts k)))
            ≡[ ap (λ t → g(c , t)) (funext λ k →
              hcls {i + index (ar Σ c) k} {a} (ts k))]
              g (_<~_ {{oc∙{Σ}}} i a (c , λ k → rec (ts k)))
            ≡[ oc-hom-close _ ]
              (i <~ a) (g(c , λ k → rec (ts k)))
            qed

----------------------------------------------------------------------
-- Freshness in Trm Σ versus free variables [Proposition 4.2]
----------------------------------------------------------------------
fv : {Σ : Sig} → Trm Σ → Fset 𝔸 -- Equation (66)
fv (bvar i)  = Ø
fv (fvar a)  = [ a ]
fv (op(c , ts)) = ⋃ λ k → fv (ts k)

-- a # t ↔ a ∉ fv t
module FreeVar {Σ : Sig} where
  #→∉ :
    (a : 𝔸)
    (t : Trm Σ)
    → --------------
    a # t → a ∉ fv t
  #→∉ a (bvar i) _ = ∉Ø
  #→∉ a (fvar b) p with a ≐ b
  ... | neq f = ∉[]{x' = b}{{¬≡→≠ f}}
  ... | equ with () ← p
  #→∉ a (op(c , ts)) p with f ← op-inj p =
    ∉⋃′ ( λ k → fv (ts k)) λ k → #→∉ a (ts k) (#1 {j = 0} (f k))

  ∉→# :
    (a : 𝔸)
    (t : Trm Σ)
    → --------------
    a ∉ fv t → a # t
  ∉→# a (bvar _) ∉Ø = refl
  ∉→# a (fvar b) (∉[]{{p}}) rewrite p = refl
  ∉→# a (op(c , ts)) p =
    ap (λ ts' → op(c , ts'))
    (funext λ k → #1 (∉→# a (ts k) (∉⋃ (fv ∘ ts) k {{p}})))

----------------------------------------------------------------------
-- Local closedness in Trm Σ [Proposition 4.3]
----------------------------------------------------------------------
data lc-at {Σ : Sig}(i : ℕ) : Trm Σ → Set where
  lc-at-bvar :
    {j : ℕ}
    {{_ : j < i}}
    → --------------
    lc-at i (bvar j)
  lc-at-fvar :
    {a : 𝔸}
    → --------------
    lc-at i (fvar a)
  lc-at-op :
    {c : Op Σ}
    {ts : Fin (length (ar Σ c)) → Trm Σ}
    (_ : ∀ k → lc-at (i + index (ar Σ c) k) (ts k))
    → ---------------------------------------------
    lc-at i (op(c , ts))

-- i ≻ t ↔ lc-at i t
module LocalClosed {Σ : Sig} where
  ≻→lc-at :
    (i : ℕ)
    (t : Trm Σ)
    → ---------------
    i ≻ t → lc-at i t
  ≻→lc-at i (bvar j) i≻bvarj = lc-at-bvar{{trich' p}}
    where
    p : ¬ i ≤ j
    p i≤j
      with q ← π₂ (i≻bvarj j {{i≤j}})
      rewrite dec-equ j
      with () ← q
  ≻→lc-at _ (fvar _) _ = lc-at-fvar
  ≻→lc-at i (op(c , ts)) p = lc-at-op λ k →
    ≻→lc-at (i + index (ar Σ c) k) (ts k) (≻Trm′ c ts i p k)

  lc-at→≻ :
    (i : ℕ)
    (t : Trm Σ)
    → ---------------
    lc-at i t → i ≻ t
  lc-at→≻ _ (bvar j) lc-at-bvar k {{p}}
    rewrite <→≠ j k (<≤ it p) = (new Ø , refl)
  lc-at→≻ _ (fvar _) lc-at-fvar _ = (new Ø , refl)
  lc-at→≻ i (op(c , ts)) (lc-at-op f) =
    ≻Trm c ts i λ k → lc-at→≻ (i + index (ar Σ c) k) (ts k) (f k)

----------------------------------------------------------------------
-- Example 4.4
----------------------------------------------------------------------
module DenotationsViaInitiality
  {- For simplicity we use Agda types in place of domains -}
  (D : Set)
  (apD : D → D → D)
  (lmD : (D → D) → D)
  where
  CD : Set -- Equation (67)
  CD = (ℕ𝔸 → D) → D

  -- CD is an oc-set
  ocCD : oc CD
  _~>_ {{ocCD}} i a κ ρ = κ (ρ ∘ (i ~> a))
  _<~_ {{ocCD}} i a κ ρ = κ (ρ ∘ (i <~ a))
  oc₁ {{ocCD}} i a b κ =
    funext λ ρ → ap κ (funext λ c → ap ρ (oc₁ i a b c))
  oc₂ {{ocCD}} i j a κ =
    funext λ ρ → ap κ (funext λ b → ap ρ (oc₂ i j a b))
  oc₃ {{ocCD}} i a κ =
    funext λ ρ →  ap κ (funext λ b → ap ρ (oc₃ i a b))
  oc₄ {{ocCD}} i a κ =
    funext λ ρ →  ap κ (funext λ b → ap ρ (oc₄ i a b))
  oc₅ {{ocCD}} i j a b κ =
    funext λ ρ → ap κ (funext λ c → ap ρ (oc₅ i j a b c))
  oc₆ {{ocCD}} i j a b κ =
    funext λ ρ → ap κ (funext λ c → ap ρ (oc₆ i j a b c))
  oc₇ {{ocCD}} i j a b κ =
    funext λ ρ → ap κ (funext λ c → ap ρ (oc₇ i j a b c))
  oc.oc₈ ocCD i j a b κ =
    funext λ ρ → ap κ (funext λ c → ap ρ (oc₈ i j a b c))
  oc.oc₉ ocCD i j a b κ =
    funext λ ρ → ap κ (funext λ c → ap ρ (oc₉ i j a b c))

  infix 6 [[_,_]]
  [[_,_]] : (ℕ𝔸 → D) → D → ℕ𝔸 → D
  [[ ρ , d ]] (ι₁ 0)      = d
  [[ ρ , d ]] (ι₁ (i +1)) = ρ (ι₁ i)
  [[ ρ , d ]] (ι₂ a)      = ρ (ι₂ a)

  [[,]]∘+1~>≡[[∘i~>,]] :
    (ρ : ℕ𝔸 → D)
    (d : D)
    (a : 𝔸)
    (i : ℕ)
    (jb : ℕ𝔸)
    → ------------------------------------------------------
    [[ ρ , d ]] ((i +1 ~> a) jb) ≡ [[ ρ ∘ (i ~> a) , d ]] jb
  [[,]]∘+1~>≡[[∘i~>,]] ρ d a i (ι₁ 0) = refl
  [[,]]∘+1~>≡[[∘i~>,]] ρ d a i (ι₁ (j +1)) with  i ≐ j
  ... | equ   = refl
  ... | neq _ = refl
  [[,]]∘+1~>≡[[∘i~>,]] ρ d a i (ι₂ b) = refl

  [[,]]∘+1<~≡[[∘i<~,]] :
    (ρ : ℕ𝔸 → D)
    (d : D)
    (a : 𝔸)
    (i : ℕ)
    (jb : ℕ𝔸)
    → ------------------------------------------------------
    [[ ρ , d ]] ((i +1 <~ a) jb) ≡ [[ ρ ∘ (i <~ a) , d ]] jb
  [[,]]∘+1<~≡[[∘i<~,]] ρ d a i (ι₁ 0) = refl
  [[,]]∘+1<~≡[[∘i<~,]] ρ d a i (ι₁ (j +1)) = refl
  [[,]]∘+1<~≡[[∘i<~,]] ρ d a i (ι₂ b) with a ≐ b
  ... | equ   = refl
  ... | neq _ = refl

  lmCD : CD → CD -- Equation (68), ignoring finite support
  lmCD κ ρ = lmD (λ d → κ [[ ρ , d ]])

  -- lmCD is an oc-set morphism from ↑(CD) to CD
  oc-homlmCD : oc-hom {{oc↑{{ocCD}}}} {{ocCD}} lmCD
  oc-hom-open  {{oc-homlmCD}} {i} {a} κ =
    funext λ ρ → ap lmD (
    funext λ d → ap κ (funext ([[,]]∘+1~>≡[[∘i~>,]] ρ d a i)))
  oc-hom-close {{oc-homlmCD}} {i} {a} κ =
    funext λ ρ → ap lmD (
    funext λ d → ap κ (funext ([[,]]∘+1<~≡[[∘i<~,]] ρ d a i)))

  apCD : CD × CD → CD -- Equation (69), ignoring finite support
  apCD (κ , κ') ρ = apD (κ ρ) (κ' ρ)

  -- apCD is an oc-Set morphism from CD × CD to CD
  oc-homapCD : oc-hom{{oc×{{ocCD}}{{ocCD}}}}{{ocCD}} apCD
  oc-hom-open  {{oc-homapCD}} (κ , κ') =
    funext λ ρ → ap₂ apD
      (ap κ  (funext (λ _ → refl)))
      (ap κ' (funext (λ _ → refl)))
  oc-hom-close {{oc-homapCD}} (κ , κ') =
    funext λ ρ → ap₂ apD
      (ap κ  (funext (λ _ → refl)))
      (ap κ' (funext (λ _ → refl)))

  vrCD : ℕ𝔸 → CD -- Equation (70), ignoring finite support
  vrCD na ρ = ρ na

  -- vrCD is an oc-set morphism from ℕ𝔸 to CD
  oc-homvrCD : oc-hom{{ocℕ𝔸}}{{ocCD}} vrCD
  oc-hom-open  {{oc-homvrCD}} _ = funext λ _ → refl
  oc-hom-close {{oc-homvrCD}} _ = funext λ _ → refl

  -- lmCD and apCD combine to give a ΛSig-algebra structure for CD
  alg : ΛSig ∙ CD → CD
  alg (Λlam , f) = lmCD (f zero)
  alg (Λapp , f) = apCD (f zero , f (succ zero))

  -- The unique alegra morphism from the intial algebra Trm (ΛSig)
  infix 6 ⟦_⟧
  ⟦_⟧ : Trm (ΛSig) → CD
  ⟦_⟧ = UniversalProperty.rec vrCD alg
