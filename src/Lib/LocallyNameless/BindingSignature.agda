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

open import Lib.Prelude renaming (_∙_ to _∙ᵖ_)
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets
open import Lib.LocallyNameless.Freshness
open import Lib.LocallyNameless.LocalClosedness
open import Lib.LocallyNameless.Support
open import Lib.LocallyNameless.AbstractionConcretion
open import Lib.LocallyNameless.RenamingReindexingSwapping
open import Lib.LocallyNameless.Category
open import Lib.LocallyNameless.Shift

open import Data.Nat.Properties
  using (+-inj ; +-preserves-≤r ; +-≤l ; +-≤r ; monus-swapr ; monus-inversel)
  renaming (+-commutative to +-comm)

open NatOrd
open VecSyntax
open FinsetSyntax

private
  +-inj' : ∀ k x y → x + k ≡ y + k → x ≡ y
  +-inj' k x y p = +-inj k x y (+-comm k x ∙ᵖ p ∙ᵖ +-comm y k)

  monus-preserves-≤ : ∀ x y z → x ≤ y → x - z ≤ y - z
  monus-preserves-≤ x y zero H≤ = H≤
  monus-preserves-≤ zero y (suc z) H≤ = 0≤x
  monus-preserves-≤ (suc x) (suc y) (suc z) (s≤s H≤) = monus-preserves-≤ x y z H≤

  monus-adj : ∀ x y z → x + y ≤ z → x ≤ z - y
  monus-adj x y z H≤ =
    subst (λ x → x ≤ z - y) (sym $ monus-swapr _ y _ refl)
    (monus-preserves-≤ (x + y) z y H≤)

  Max : {n : Nat} → Nat ^ n → Nat
  Max = foldr max 0

  ≤-Max :
    {n : Nat}
    (f : Nat ^ n)
    (k : Fin n)
    → -------------
    f k ≤ Max f
  ≤-Max f k with fin-view k
  ... | zero  = max-≤l _ _
  ... | suc k = ≤-trans (≤-Max (tail f) k) (max-≤r _ _)

----------------------------------------------------------------------
-- Plotkin's binding signatures [Section 4.1]
----------------------------------------------------------------------
record Sig : Type₁ where
  constructor mkSig
  field
    Op : Type
    ar : Op → Array Nat

open Sig public

-- Example: the binding signature for untyped λ-terms
ΛSig : Sig
ΛSig = mkSig ΛOp ΛAr
  module _ where
    data ΛOp : Type where
      Λlam : ΛOp
      Λapp : ΛOp
    ΛAr : ΛOp → Array Nat
    length (ΛAr Λlam) = 1
    length (ΛAr Λapp) = 2
    index (ΛAr Λlam)  = lookup (1 ∷ [])
    index (ΛAr Λapp)  = lookup (0 ∷ 0 ∷ [])

----------------------------------------------------------------------
-- Set functor associated with a signature
----------------------------------------------------------------------
infixr 8 _∙_ _∙′_
_∙_ : Sig → Type → Type
Σ ∙ X  = Σ[ c ∈ Op Σ ] (X ^ length (ar Σ c)) -- Equation (58)

_∙′_ : (Σ : Sig){X Y : Type} → (X → Y) → Σ ∙ X → Σ ∙ Y
(Σ ∙′ f) (c , t) = c , (f ∘ t)

-- Action of Σ ∙_ on locally nameless sets
instance
  oc∙ :
    {Σ : Sig}
    {X : Type}
    ⦃ _ : oc X ⦄
    → ----------
    oc (Σ ∙ X)
  _~>_ ⦃ oc∙{Σ} ⦄ i a (c , t) =
    (c , λ k → (i + index (ar Σ c) k ~> a)(t k))
  _<~_ ⦃ oc∙{Σ} ⦄ i a (c , t) =
    (c , λ k → (i + index (ar Σ c) k <~ a)(t k))
  oc₁ ⦃ oc∙{Σ} ⦄ i a b (c , t) = ap (c ,_) (funext λ k →
    oc₁ (i + index (ar Σ c) k) a b (t k))
  oc₂ ⦃ oc∙{Σ} ⦄ i j a (c , t) = ap (c ,_) (funext λ k →
    oc₂ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a (t k))
  oc₃ ⦃ oc∙{Σ} ⦄ i a (c , t) = ap (c ,_) (funext λ k →
    oc₃ (i + index (ar Σ c) k) a (t k))
  oc₄ ⦃ oc∙{Σ} ⦄ i a (c , t) = ap (c ,_) (funext λ k →
    oc₄ (i + index (ar Σ c) k) a (t k))
  oc₅ ⦃ oc∙{Σ} ⦄ i j a b (c , t) = ap (c ,_) (funext λ k →
    oc₅ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a b (t k)
    ⦃ inj≠ (+-inj' (index (ar Σ c) k) _ _) auto ⦄)
  oc₆ ⦃ oc∙{Σ} ⦄ i j a b (c , t) = ap (c ,_) (funext λ k →
    oc₆ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a  b (t k))
  oc₇ ⦃ oc∙{Σ} ⦄ i  j a b (c , t) = ap (c ,_) (funext λ k →
    oc₇ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a b (t k)
    ⦃ inj≠ (+-inj' (index (ar Σ c) k) _ _) auto ⦄)
  oc₈ ⦃ oc∙{Σ} ⦄ i j a b (c , t) = ap (c ,_) (funext λ k →
    oc₈ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a  b (t k))
  oc₉ ⦃ oc∙{Σ} ⦄ i j a b (c , t) = ap (c ,_) (funext λ k →
    oc₉ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a  b (t k))

#oc∙ :
  {Σ : Sig}
  {X : Type}
  ⦃ _ : oc X ⦄
  {c : Op Σ}
  {f : X ^ length (ar Σ c)}
  (a : 𝔸)
  (_ : ∀ k → a # f k)
  → ----------------------------
  _#_ ⦃ oc∙{Σ} ⦄ a (c , f)
#oc∙ {Σ} {c = c} a g = ap (c ,_) (funext λ k → #1 (g k))

≻oc∙ :
  {Σ : Sig}
  {X : Type}
  ⦃ _ : oc X ⦄
  {c : Op Σ}
  {f : X ^ length (ar Σ c)}
  (i : Nat)
  (_ : ∀ k → i + index (ar Σ c) k ≻ f k)
  → ------------------------------------
  _≻_ ⦃ oc∙{Σ} ⦄ i (c , f)
≻oc∙ {Σ} {c = c} i g j =
  (new Ø , ap (c ,_) (funext λ k → ≻3 (g k) (+-preserves-≤r i j _ auto)))

instance
  lns∙ :
    {Σ : Sig}
    {X : Type}
    ⦃ _ : lns X ⦄
    → -----------
    lns (Σ ∙ X)
  ocSet ⦃ lns∙{Σ} ⦄ = oc∙{Σ}
  asupp ⦃ lns∙{Σ} ⦄ (c , f) = Иi
    (⋃ λ k →  Иe₁ (asupp (f k)))
    λ a → #oc∙ {Σ} a λ k → Иe₂ (asupp (f k)) a ⦃ ∉⋃ _ k ⦄
  isupp ⦃ lns∙{Σ} ⦄ (c , f) =
    let i = Max λ k → fst (isupp (f k)) in
    (i , ≻oc∙ {Σ} i λ k →  ≻1 (≤-trans (≤-Max _ k) (+-≤l _ _)) (snd (isupp (f k))))

-- Action of Σ ∙′_ on morphisms of locally nameless sets
instance
  oc∙′ :
    {Σ : Sig}
    {X Y : Type}
    ⦃ ocX : oc X ⦄
    ⦃ ocY : oc Y ⦄
    {φ : X → Y}
    ⦃ _ : oc-hom φ ⦄
    → -----------------------------------
    oc-hom ⦃ oc∙{Σ} ⦄ ⦃ oc∙{Σ} ⦄ (Σ ∙′ φ)
  oc-hom-open ⦃ oc∙′ ⦄ (c , _) =
    ap (c ,_) (funext λ _ → oc-hom-open _)
  oc-hom-close ⦃ oc∙′ ⦄ (c , _) =
    ap (c ,_) (funext λ _ → oc-hom-close _)

  lns∙′ :
    {Σ : Sig}
    {X Y : Type}
    ⦃ lnsX : lns X ⦄
    ⦃ lnsY : lns Y ⦄
    {φ : X → Y}
    ⦃ _ : lns-hom φ ⦄
    → --------------------------------------
    lns-hom ⦃ lns∙{Σ} ⦄ ⦃ lns∙{Σ} ⦄ (Σ ∙′ φ)
  ochom ⦃ lns∙′ ⦄ = oc∙′

----------------------------------------------------------------------
-- Terms over a binding signature [Equation (65)]
----------------------------------------------------------------------
data Trm (Σ : Sig) : Type where
  var : Nat𝔸 → Trm Σ
  op  : Σ ∙ Trm Σ → Trm Σ

pattern bvar i = var (inl i)
pattern fvar a = var (inr a)

op-inj :
  {Σ : Sig}
  {c c' : Op Σ}
  {ts  : Trm Σ ^ length (ar Σ c)}
  {ts' : Trm Σ ^ length (ar Σ c')}
  (_ : op(c , ts) ≡ op(c' , ts'))
  → --------------------------------------
  (c , ts) ≡ (c' , ts')
op-inj {Σ} {c} {ts = ts} p = ap f p where
  f : Trm Σ → Σ[ c ∈ Op Σ ] (Trm Σ ^ length (ar Σ c))
  f (op(c , ts)) = (c , ts)
  f (var _)      = (c , ts)

op-inj' :
  {Σ : Sig}
  {c : Op Σ}
  {ts ts'  : Trm Σ ^ length (ar Σ c)}
  (_ : op(c , ts) ≡ op(c , ts'))
  → --------------------------------------
  ts ≡ ts'
op-inj' p i = let bar = ap fst (op-inj p) i ; foo = ap snd (op-inj p) i in {!!}

----------------------------------------------------------------------
-- The terms form a locally nameless set
----------------------------------------------------------------------
-- The oc-Set structure
instance
  ocTrm : {Σ : Sig} → oc (Trm Σ)
  ocTrm {Σ} = mkoc opn cls ax₁ ax₂ ax₃ ax₄ ax₅ ax₆ ax₇ ax₈ ax₉
    where
    X = Trm Σ
    opn : Nat → 𝔸 → X → X
    opn i a (var v)   = var ((i ~> a) v)
    opn i a (op(c , ts)) =
      op(c , λ k → opn (i + index (ar Σ c) k) a (ts k))
    cls : Nat → 𝔸 → X → X
    cls i a (var v)   = var ((i <~ a) v)
    cls i a (op(c , ts)) =
      op(c , λ k → cls (i + index (ar Σ c) k) a (ts k))
    ax₁ :
      (i : Nat)
      (a b : 𝔸)
      (t : Trm Σ)
      → -----------------------------
      opn i a (opn i b t) ≡ opn i b t
    ax₁ i a b (var v) = ap var (oc₁ i a b v)
    ax₁ i a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₁ (i + index (ar Σ c) k) a b (ts k))
    ax₂ :
      (i j : Nat)
      (a : 𝔸)
      (t : Trm Σ)
      → -----------------------------
      cls i a (cls j a t) ≡ cls j a t
    ax₂ i j a (var v) = ap var (oc₂ i j a v)
    ax₂ i j a (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₂ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a (ts k))
    ax₃ :
      (i : Nat)
      (a : 𝔸)
      (t : Trm Σ)
      → -----------------------------
      cls i a (opn i a t) ≡ cls i a t
    ax₃ i a (var v) = ap var (oc₃ i a v)
    ax₃ i a (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₃ (i + index (ar Σ c) k) a (ts k))
    ax₄ :
      (i : Nat)
      (a : 𝔸)
      (t : Trm Σ)
      → -----------------------------
      opn i a (cls i a t) ≡ opn i a t
    ax₄ i a (var v) = ap var (oc₄ i a v)
    ax₄ i a (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₄ (i + index (ar Σ c) k) a (ts k))
    ax₅ :
      (i j : Nat)
      (a b : 𝔸)
      (t : Trm Σ)
      ⦃ _ : i ≠ j ⦄
      → ---------------------------------------
      opn i a (opn j b t) ≡ opn j b (opn i a t)
    ax₅ i j a b (var v) = ap var (oc₅ i j a b v)
    ax₅ i j a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₅ (i + index (ar Σ c) k)
          (j + index (ar Σ c) k) a b (ts k)
          ⦃ inj≠ (+-inj' (index (ar Σ c) k) _ _) auto ⦄)
    ax₆ :
      (i j : Nat)
      (a b : 𝔸)
      (t : Trm Σ)
      ⦃ _ : a ≠ b ⦄
      → ---------------------------------------
      cls i a (cls j b t) ≡ cls j b (cls i a t)
    ax₆ i j a b (var v) = ap var (oc₆ i j a b v)
    ax₆ i j a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₆ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a b (ts k))
    ax₇ :
      (i j : Nat)
      (a b : 𝔸)
      (t : Trm Σ)
      ⦃ _ : i ≠ j ⦄
      ⦃ _ : a ≠ b ⦄
      → ---------------------------------------
      opn i a (cls j b t) ≡ cls j b (opn i a t)
    ax₇ i j a b (var v) = ap var (oc₇ i j a b v)
    ax₇ i j a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₇ (i + index (ar Σ c) k)
          (j + index (ar Σ c) k) a b (ts k)
          ⦃ inj≠ (+-inj' (index (ar Σ c) k) _ _) auto ⦄)
    ax₈ :
      (i j : Nat)
      (a b : 𝔸)
      (t : Trm Σ)
      → -----------------------------------------------------------
      opn i b (cls i a (opn j b t)) ≡ opn j b (cls j a (opn i a t))
    ax₈ i j a b (var v) = ap var (oc₈ i j a b v)
    ax₈ i j a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₈ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a b (ts k))
    ax₉ :
      (i j : Nat)
      (a b : 𝔸)
      (t : Trm Σ)
      → -----------------------------------------------------------
      cls j a (opn i a (cls j b t)) ≡ cls j b (opn i b (cls i a t))
    ax₉ i j a b (var v) = ap var (oc₉ i j a b v)
    ax₉ i j a b (op(c , ts)) = ap (λ ts' → op(c , ts')) (funext λ k →
      ax₉ (i + index (ar Σ c) k) (j + index (ar Σ c) k) a b (ts k))

-- A lemma about atom-support in Trm Σ
#Trm :
  {Σ : Sig}
  (c : Op Σ)
  (ts : Trm Σ ^ length (ar Σ c))
  (a : 𝔸)
  (_ : ∀ k → a # ts k)
  → ----------------------------------
   a # op(c , ts)
#Trm {Σ} c ts a f = ap (λ ts' → op(c , ts')) (funext λ k → #1 (f k))

-- Lemmas about index-support in Trm Σ
≻Trm :
  {Σ : Sig}
  (c : Op Σ)
  (ts : Trm Σ ^ length (ar Σ c))
  (i : Nat)
  (_ : ∀ k → i + index (ar Σ c) k ≻ ts k)
  → -------------------------------------
  i ≻ op(c , ts)
≻Trm {Σ} c ts i f j = (new Ø , ap (λ ts' →
  op(c , ts')) (funext λ k → ≻3 (f k) (+-preserves-≤r i j _ auto)))

≻Trm′ :
  {Σ : Sig}
  (c : Op Σ)
  (ts : Trm Σ ^ length (ar Σ c))
  (i : Nat)
  (_ : i ≻ op(c , ts))
  (k : Fin (length (ar Σ c)))
  → ----------------------------------
  i + index (ar Σ c) k ≻ ts k
≻Trm′ {Σ} c ts i p k j
  with (a , q) ← p (j - index (ar Σ c) k) ⦃ monus-adj _ _ _ auto ⦄ = (a , e')
  where
  H≡ : j - index (ar Σ c) k + index (ar Σ c) k ≡ j
  H≡ = +-comm _ (index (ar Σ c) k) ∙ᵖ monus-inversel j (index (ar Σ c) k) (≤-trans (+-≤r _ _) auto)
  e' : (j ~> a)(ts k) ≡ ts k
  e' =
    (j ~> a)(ts k)                                         ≡˘⟨ ap (λ j' → (j' ~> a)(ts k)) H≡ ⟩
    ((j - index (ar Σ c) k + index (ar Σ c) k) ~> a)(ts k) ≡⟨ {!!} ⟩
    ts k                                                   ∎

-- -- The finite support properties
-- lnsTrm : {Σ : Sig} → lns (Trm Σ)
-- lnsTrm {Σ} = mklns asp isp
--   where
--   instance
--     _ : lns Nat𝔸
--     _ = lnsNat𝔸
--   asp : (t : Trm Σ) → И a ∶ 𝔸 , a # t
--   asp (var v) with Иi и₁ и₂ ← asupp v =
--     Иi и₁ (λ a → ap var (и₂ a))
--   asp (op(c , ts)) = Иi
--     (⋃ λ k →  Иe₁ (asp (ts k)))
--     (λ a → #Trm c ts a λ k → Иe₂ (asp (ts k)) a ⦃ ∉⋃ _ k ⦄)
--   isp : (t : Trm Σ) → ∑ i ∶ Nat , i ≻ t
--   isp (var v) with (i , p) ← isupp v =
--     (i , λ j → (π₁ (p j)) , ap var (π₂ (p j)))
--   isp (op(c , ts)) =
--     let i = Max λ k →  π₁ (isp (ts k)) in
--     (i ,  ≻Trm c ts i λ k → ≻1 (≤+ _ (≤Max _ k)) (π₂ (isp (ts k))) )

-- ----------------------------------------------------------------------
-- -- The locally nameless set Trm Σ is the free Σ∙_-algebra on Nat𝔸
-- -- [Theorem 4.1]
-- ----------------------------------------------------------------------
-- module UniversalProperty
--   {- We can prove the universal property with respect to all oc-sets
--      X, rather than just locally nameless ones. -}
--   {Σ : Sig}
--   {X : Type}
--   (f : Nat𝔸 → X)
--   (g : Σ ∙ X → X)
--   where
--   instance
--     _ : lns Nat𝔸
--     _ = lnsNat𝔸
--     _ : lns (Trm Σ)
--     _ = lnsTrm
--   -- Existence
--   rec : Trm Σ → X
--   rec (var v)      = f v
--   rec (op(c , ts)) = g (c , λ k → rec (ts k))
--   -- Uniqueness [Equation (61)]
--   module _
--     (h : Trm Σ → X)
--     (hvar : ∀ v → h (var v) ≡ f v)
--     (hop : ∀ x → h(op x) ≡ g ((Σ ∙′ h) x))
--     where
--     uniq : h ≡ rec
--     uniq = funext uniq'
--       where
--       uniq' : ∀ t → h t ≡ rec t
--       uniq' (var v) = hvar v
--       uniq' (op(c , ts)) =
--         proof
--           h (op (c , ts))
--         ≡[ hop (c , ts) ]
--           g ((Σ ∙′ h)(c , ts))
--         ≡[]
--           g (c , (h ∘ ts))
--         ≡[ ap (λ x → g (c , x)) (funext λ k → uniq' (ts k)) ]
--           g (c , λ k → rec (ts k))
--         qed

--     -- If we assume X is also an oc-set and that
--     -- f, g and h are morphisms of oc-sets...
--     module _
--       ⦃ _ : oc X ⦄
--       ⦃ homf : oc-hom f ⦄
--       ⦃ homg : oc-hom ⦃ oc∙{Σ} ⦄ g ⦄
--       ⦃ _ : oc-hom h ⦄
--       where
--     -- ...then rec is also a morphism
--         rec-hom : oc-hom rec
--         rec-hom = mkoc-hom hopn hcls
--           where
--           hopn :
--             {i : Nat}
--             {a : 𝔸}
--             (t : Trm Σ)
--             → --------------------------------
--             rec ((i ~> a)t) ≡ (i ~> a) (rec t)
--           hopn (var v) = oc-hom-open v
--           hopn {i} {a} (op(c , ts)) =
--             proof
--               g (c , λ k → rec ((i + index (ar Σ c) k ~> a)(ts k)))
--             ≡[ ap (λ t → g(c , t)) (funext λ k →
--               hopn {i + index (ar Σ c) k} {a} (ts k))]
--               g (_~>_ ⦃ oc∙{Σ} ⦄ i a (c , λ k → rec (ts k)))
--             ≡[ oc-hom-open _ ]
--               (i ~> a) (g (c , λ k → rec (ts k)))
--             qed
--           hcls :
--             {i : Nat}
--             {a : 𝔸}
--             (t : Trm Σ)
--             → --------------------------------
--             rec ((i <~ a)t) ≡ (i <~ a) (rec t)
--           hcls (var v) = oc-hom-close v
--           hcls {i} {a} (op(c , ts)) =
--             proof
--               g (c , λ k → rec ((i + index (ar Σ c) k <~ a)(ts k)))
--             ≡[ ap (λ t → g(c , t)) (funext λ k →
--               hcls {i + index (ar Σ c) k} {a} (ts k))]
--               g (_<~_ ⦃ oc∙{Σ} ⦄ i a (c , λ k → rec (ts k)))
--             ≡[ oc-hom-close _ ]
--               (i <~ a) (g(c , λ k → rec (ts k)))
--             qed

-- ----------------------------------------------------------------------
-- -- Freshness in Trm Σ versus free variables [Proposition 4.2]
-- ----------------------------------------------------------------------
-- fv : {Σ : Sig} → Trm Σ → Fset 𝔸 -- Equation (66)
-- fv (bvar i)  = Ø
-- fv (fvar a)  = [ a ]
-- fv (op(c , ts)) = ⋃ λ k → fv (ts k)

-- -- a # t ↔ a ∉ fv t
-- module FreeVar {Σ : Sig} where
--   #→∉ :
--     (a : 𝔸)
--     (t : Trm Σ)
--     → --------------
--     a # t → a ∉ fv t
--   #→∉ a (bvar i) _ = ∉Ø
--   #→∉ a (fvar b) p with a ≐ b
--   ... | neq f = ∉[]{x' = b}⦃ ¬≡→≠ f ⦄
--   ... | equ with () ← p
--   #→∉ a (op(c , ts)) p with f ← op-inj p =
--     ∉⋃′ ( λ k → fv (ts k)) λ k → #→∉ a (ts k) (#1 {j = 0} (f k))

--   ∉→# :
--     (a : 𝔸)
--     (t : Trm Σ)
--     → --------------
--     a ∉ fv t → a # t
--   ∉→# a (bvar _) ∉Ø = refl
--   ∉→# a (fvar b) (∉[]⦃ p ⦄) rewrite p = refl
--   ∉→# a (op(c , ts)) p =
--     ap (λ ts' → op(c , ts'))
--     (funext λ k → #1 (∉→# a (ts k) (∉⋃ (fv ∘ ts) k ⦃ p ⦄)))

-- ----------------------------------------------------------------------
-- -- Local closedness in Trm Σ [Proposition 4.3]
-- ----------------------------------------------------------------------
-- data lc-at {Σ : Sig}(i : Nat) : Trm Σ → Type where
--   lc-at-bvar :
--     {j : Nat}
--     ⦃ _ : j < i ⦄
--     → --------------
--     lc-at i (bvar j)
--   lc-at-fvar :
--     {a : 𝔸}
--     → --------------
--     lc-at i (fvar a)
--   lc-at-op :
--     {c : Op Σ}
--     {ts : Fin (length (ar Σ c)) → Trm Σ}
--     (_ : ∀ k → lc-at (i + index (ar Σ c) k) (ts k))
--     → ---------------------------------------------
--     lc-at i (op(c , ts))

-- -- i ≻ t ↔ lc-at i t
-- module LocalClosed {Σ : Sig} where
--   ≻→lc-at :
--     (i : Nat)
--     (t : Trm Σ)
--     → ---------------
--     i ≻ t → lc-at i t
--   ≻→lc-at i (bvar j) i≻bvarj = lc-at-bvar⦃ trich' p ⦄
--     where
--     p : ¬ i ≤ j
--     p i≤j
--       with q ← π₂ (i≻bvarj j ⦃ i≤j ⦄)
--       rewrite dec-equ j
--       with () ← q
--   ≻→lc-at _ (fvar _) _ = lc-at-fvar
--   ≻→lc-at i (op(c , ts)) p = lc-at-op λ k →
--     ≻→lc-at (i + index (ar Σ c) k) (ts k) (≻Trm′ c ts i p k)

--   lc-at→≻ :
--     (i : Nat)
--     (t : Trm Σ)
--     → ---------------
--     lc-at i t → i ≻ t
--   lc-at→≻ _ (bvar j) lc-at-bvar k ⦃ p ⦄
--     rewrite <→≠ j k (<≤ it p) = (new Ø , refl)
--   lc-at→≻ _ (fvar _) lc-at-fvar _ = (new Ø , refl)
--   lc-at→≻ i (op(c , ts)) (lc-at-op f) =
--     ≻Trm c ts i λ k → lc-at→≻ (i + index (ar Σ c) k) (ts k) (f k)

-- ----------------------------------------------------------------------
-- -- Example 4.4
-- ----------------------------------------------------------------------
-- module DenotationsViaInitiality
--   {- For simplicity we use Agda types in place of domains -}
--   (D : Type)
--   (apD : D → D → D)
--   (lmD : (D → D) → D)
--   where
--   CD : Type -- Equation (67)
--   CD = (Nat𝔸 → D) → D

--   -- CD is an oc-set
--   ocCD : oc CD
--   _~>_ ⦃ ocCD ⦄ i a κ ρ = κ (ρ ∘ (i ~> a))
--   _<~_ ⦃ ocCD ⦄ i a κ ρ = κ (ρ ∘ (i <~ a))
--   oc₁ ⦃ ocCD ⦄ i a b κ =
--     funext λ ρ → ap κ (funext λ c → ap ρ (oc₁ i a b c))
--   oc₂ ⦃ ocCD ⦄ i j a κ =
--     funext λ ρ → ap κ (funext λ b → ap ρ (oc₂ i j a b))
--   oc₃ ⦃ ocCD ⦄ i a κ =
--     funext λ ρ →  ap κ (funext λ b → ap ρ (oc₃ i a b))
--   oc₄ ⦃ ocCD ⦄ i a κ =
--     funext λ ρ →  ap κ (funext λ b → ap ρ (oc₄ i a b))
--   oc₅ ⦃ ocCD ⦄ i j a b κ =
--     funext λ ρ → ap κ (funext λ c → ap ρ (oc₅ i j a b c))
--   oc₆ ⦃ ocCD ⦄ i j a b κ =
--     funext λ ρ → ap κ (funext λ c → ap ρ (oc₆ i j a b c))
--   oc₇ ⦃ ocCD ⦄ i j a b κ =
--     funext λ ρ → ap κ (funext λ c → ap ρ (oc₇ i j a b c))
--   oc.oc₈ ocCD i j a b κ =
--     funext λ ρ → ap κ (funext λ c → ap ρ (oc₈ i j a b c))
--   oc.oc₉ ocCD i j a b κ =
--     funext λ ρ → ap κ (funext λ c → ap ρ (oc₉ i j a b c))

--   infix 6 [[_,_]]
--   [[_,_]] : (Nat𝔸 → D) → D → Nat𝔸 → D
--   [[ ρ , d ]] (ι₁ 0)      = d
--   [[ ρ , d ]] (ι₁ (i +1)) = ρ (ι₁ i)
--   [[ ρ , d ]] (ι₂ a)      = ρ (ι₂ a)

--   [[,]]∘+1~>≡[[∘i~>,]] :
--     (ρ : Nat𝔸 → D)
--     (d : D)
--     (a : 𝔸)
--     (i : Nat)
--     (jb : Nat𝔸)
--     → ------------------------------------------------------
--     [[ ρ , d ]] ((i +1 ~> a) jb) ≡ [[ ρ ∘ (i ~> a) , d ]] jb
--   [[,]]∘+1~>≡[[∘i~>,]] ρ d a i (ι₁ 0) = refl
--   [[,]]∘+1~>≡[[∘i~>,]] ρ d a i (ι₁ (j +1)) with  i ≐ j
--   ... | equ   = refl
--   ... | neq _ = refl
--   [[,]]∘+1~>≡[[∘i~>,]] ρ d a i (ι₂ b) = refl

--   [[,]]∘+1<~≡[[∘i<~,]] :
--     (ρ : Nat𝔸 → D)
--     (d : D)
--     (a : 𝔸)
--     (i : Nat)
--     (jb : Nat𝔸)
--     → ------------------------------------------------------
--     [[ ρ , d ]] ((i +1 <~ a) jb) ≡ [[ ρ ∘ (i <~ a) , d ]] jb
--   [[,]]∘+1<~≡[[∘i<~,]] ρ d a i (ι₁ 0) = refl
--   [[,]]∘+1<~≡[[∘i<~,]] ρ d a i (ι₁ (j +1)) = refl
--   [[,]]∘+1<~≡[[∘i<~,]] ρ d a i (ι₂ b) with a ≐ b
--   ... | equ   = refl
--   ... | neq _ = refl

--   lmCD : CD → CD -- Equation (68), ignoring finite support
--   lmCD κ ρ = lmD (λ d → κ [[ ρ , d ]])

--   -- lmCD is an oc-set morphism from ↑(CD) to CD
--   oc-homlmCD : oc-hom ⦃ oc↑⦃ ocCD ⦄ ⦄ ⦃ ocCD ⦄ lmCD
--   oc-hom-open  ⦃ oc-homlmCD ⦄ {i} {a} κ =
--     funext λ ρ → ap lmD (
--     funext λ d → ap κ (funext ([[,]]∘+1~>≡[[∘i~>,]] ρ d a i)))
--   oc-hom-close ⦃ oc-homlmCD ⦄ {i} {a} κ =
--     funext λ ρ → ap lmD (
--     funext λ d → ap κ (funext ([[,]]∘+1<~≡[[∘i<~,]] ρ d a i)))

--   apCD : CD × CD → CD -- Equation (69), ignoring finite support
--   apCD (κ , κ') ρ = apD (κ ρ) (κ' ρ)

--   -- apCD is an oc-Set morphism from CD × CD to CD
--   oc-homapCD : oc-hom⦃ oc×⦃ ocCD ⦄⦃ ocCD ⦄ ⦄⦃ ocCD ⦄ apCD
--   oc-hom-open  ⦃ oc-homapCD ⦄ (κ , κ') =
--     funext λ ρ → ap₂ apD
--       (ap κ  (funext (λ _ → refl)))
--       (ap κ' (funext (λ _ → refl)))
--   oc-hom-close ⦃ oc-homapCD ⦄ (κ , κ') =
--     funext λ ρ → ap₂ apD
--       (ap κ  (funext (λ _ → refl)))
--       (ap κ' (funext (λ _ → refl)))

--   vrCD : Nat𝔸 → CD -- Equation (70), ignoring finite support
--   vrCD na ρ = ρ na

--   -- vrCD is an oc-set morphism from Nat𝔸 to CD
--   oc-homvrCD : oc-hom⦃ ocNat𝔸 ⦄⦃ ocCD ⦄ vrCD
--   oc-hom-open  ⦃ oc-homvrCD ⦄ _ = funext λ _ → refl
--   oc-hom-close ⦃ oc-homvrCD ⦄ _ = funext λ _ → refl

--   -- lmCD and apCD combine to give a ΛSig-algebra structure for CD
--   alg : ΛSig ∙ CD → CD
--   alg (Λlam , f) = lmCD (f zero)
--   alg (Λapp , f) = apCD (f zero , f (succ zero))

--   -- The unique alegra morphism from the intial algebra Trm (ΛSig)
--   infix 6 ⟦_⟧
--   ⟦_⟧ : Trm (ΛSig) → CD
--   ⟦_⟧ = UniversalProperty.rec vrCD alg
