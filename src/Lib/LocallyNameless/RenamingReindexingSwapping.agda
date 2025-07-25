--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.LocallyNameless.RenamingReindexingSwapping where

open import Lib.Prelude
open import Lib.Dec
open import Lib.Finset
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets
open import Lib.LocallyNameless.Freshness
open import Lib.LocallyNameless.LocalClosedness
open import Lib.LocallyNameless.Support
open import Lib.LocallyNameless.AbstractionConcretion

open import Data.Nat.Order using (<-not-equal)

open FinsetSyntax
open NatOrd

----------------------------------------------------------------------
-- Lemma 2.16
----------------------------------------------------------------------
module _
  {X : Type}
  ⦃ _ : lns X ⦄
  {a b : 𝔸}
  {i j : Nat}
  {x : X}
  where
  ~><~ : -- Equation (19)
    (p : i ≻ x)
    (q : j ≻ x)
    → ---------------------------------------
    (i ~> b)((i <~ a)x) ≡ (j ~> b)((j <~ a)x)
  ~><~ p q  =
    (i ~> b)((i <~ a)x)           ≡˘⟨ ap ((i ~> b) ∘ (i <~ a)) (≻3 q ≤-refl) ⟩
    (i ~> b)((i <~ a)((j ~> b)x)) ≡⟨ oc₈ _ _ _ _ _ ⟩
    (j ~> b)((j <~ a)((i ~> a)x)) ≡⟨ ap ((j ~> b) ∘ (j <~ a)) (≻3 p ≤-refl) ⟩
    (j ~> b)((j <~ a)x)           ∎

  <~~> : -- Equation (20)
    (p : a # x)
    (q : b # x)
    → ---------------------------------------
    (j <~ a)((i ~> a)x) ≡ (j <~ b)((i ~> b)x)
  <~~> p q =
    (j <~ a)((i ~> a)x)           ≡˘⟨ ap ((j <~ a) ∘ (i ~> a)) (#2 q) ⟩
    (j <~ a)((i ~> a)((j <~ b)x)) ≡⟨ oc₉ _ _ _ _ _ ⟩
    (j <~ b)((i ~> b)((i <~ a)x)) ≡⟨ ap ((j <~ b) ∘ (i ~> b)) (#2 p) ⟩
    (j <~ b)((i ~> b)x)           ∎

{- We make the following definitions abstract to reduce performance overhead
and improve readability. -}
abstract
  ----------------------------------------------------------------------
  -- Renaming
  ----------------------------------------------------------------------
  infix 5 _↤_
  _↤_ : {X : Type}⦃ _ : lns X ⦄ → 𝔸 → 𝔸 → X → X
  (b ↤ a)x =
    let i = fst (isupp x) in
    (i ~> b)((i <~ a)x) -- Equation(21)

  ↤fresh :
    {X : Type}
    ⦃ _ : lns X ⦄
    {a b : 𝔸}
    (x : X)
    (i : Nat)
    (_ : i ≻ x)
    → ----------------------------
    (b ↤ a)x ≡ (i ~> b)((i <~ a)x)
  ↤fresh x i p = ~><~ (snd (isupp x)) p

  ≻↤ :
    {X : Type}
    ⦃ _ : lns X ⦄
    (a b : 𝔸)
    (x : X)
    (i : Nat)
    (_ : i ≻ x)
    → ----------
    i ≻ (b ↤ a)x
  ≻↤ a b x i p j =
    let
      c = new ([ a ] ∪ [ b ])
      k = suc j
      k≻x : k ≻ x
      k≻x = ≻1 (≤-trans auto ≤-refl) p
      instance
        _ : c ≠ a
        _ = ∉∷₁ (unfinite ([ a ] ∪ [ b ]))
        _ : c ≠ b
        _ = ∉∷₁ (∉∷₂ (unfinite ([ a ] ∪ [ b ])))
        _ : j ≠ k
        _ = ¬≡→≠ (<-not-equal auto)
    in (c ,
      ((j ~> c)((b ↤ a)x)            ≡⟨ ap (j ~> c) (↤fresh _ _ k≻x) ⟩
       (j ~> c)((k ~> b)((k <~ a)x)) ≡⟨ oc₅ _ _ _ _ _ ⟩
       (k ~> b)((j ~> c)((k <~ a)x)) ≡⟨ ap (k ~> b) (oc₇ _ _ _ _ _) ⟩
       (k ~> b)((k <~ a)((j ~> c)x)) ≡⟨ ap ((k ~> b) ∘ (k <~ a)) (≻3 p auto) ⟩
       (k ~> b)((k <~ a)x)           ≡˘⟨ ↤fresh _ _ k≻x ⟩
       (b ↤ a)x                      ∎))

  ----------------------------------------------------------------------
  -- Re-indexing
  ----------------------------------------------------------------------

  infix 5 _↦_
  _↦_ : {X : Type}⦃ _ : lns X ⦄ → Nat → Nat → X → X
  (i ↦ j)x =
    let a = new (Иe₁ (asupp x)) in
    (j <~ a)((i ~> a)x) -- Equation (22)

  ↦fresh :
    {X : Type}
    ⦃ _ : lns X ⦄
    {i j : Nat}
    (x : X)
    (a : 𝔸)
    ⦃ _ : a # x ⦄
    → ----------------------------
    (i ↦ j)x ≡ (j <~ a)((i ~> a)x)
  ↦fresh x a =
    let
      bs = Иe₁ (asupp x)
      b  = new bs
      b#x : b # x
      b#x = Иe₂ (asupp x) b ⦃ unfinite bs ⦄
    in <~~> b#x auto

  ≻↦ :
    {X : Type}
    ⦃ _ : lns X ⦄
    (i j : Nat)
    (x : X)
    → ------------------
    i ≻ x → (i ↦ j)x ≡ x
  ≻↦ i j x p =
    let
      as = Иe₁ (asupp x)
      a  = new as
      instance
        _ : a # x
        _ = Иe₂ (asupp x) a ⦃ unfinite as ⦄
    in
    (i ↦ j)x            ≡⟨⟩
    (j <~ a)((i ~> a)x) ≡⟨ ap (j <~ a) (≻3 p ≤-refl) ⟩
    (j <~ a)x           ≡⟨ #2 auto ⟩
    x                   ∎

  ↦≻ :
    {X : Type}
    ⦃ _ : lns X ⦄
    {i j k : Nat}
    {x : X}
    (_ : k ≻ x)
    (_ : k > j)
    → -----------
    k ≻ (i ↦ j)x
  ↦≻ p q =
    ≻1 (max-univ _ _ _ ≤-refl q) (<~index-supports (~>index-supports p))

----------------------------------------------------------------------
-- Renset properties of renaming ⟨Proposition 2.17⟩
----------------------------------------------------------------------
module _ {X : Type}⦃ L : lns X ⦄{x : X} where
  abstract
    rn₁ : -- Equation (23)
      {a : 𝔸}
      → ----------
      (a ↤ a)x ≡ x
    rn₁ {a} =
      let i , i≻x = isupp x in
      (a ↤ a)x            ≡⟨⟩
      (i ~> a)((i <~ a)x) ≡⟨ oc₄ _ _ _ ⟩
      (i ~> a)x           ≡⟨ ≻3 i≻x ≤-refl ⟩
      x                   ∎

    rn₂ : -- Equation (24)
      {a b c : 𝔸}
      ⦃ _ : a ≠ c ⦄
      → --------------------------
      (b ↤ a)((c ↤ a)x) ≡ (c ↤ a)x
    rn₂ {a} {b} {c} =
      (b ↤ a)((c ↤ a)x) ≡⟨⟩
      (j ~> b)((j <~ a)((i ~> c)((i <~ a)x))) ≡⟨ ~><~ q (≻1 (max-≤r _ _) q) ⟩
      (k ~> b)((k <~ a)((i ~> c)((i <~ a)x))) ≡⟨ ap ((k ~> b) ∘ (k <~ a)) (~><~ p (≻1 (max-≤l _ _) p)) ⟩
      (k ~> b)((k <~ a)((k ~> c)((k <~ a)x))) ≡⟨ ap (k ~> b) (#2 r) ⟩
      (k ~> b)((k ~> c)((k <~ a)x))           ≡⟨ oc₁ _ _ _ _ ⟩
      (k ~> c)((k <~ a)x)                     ≡⟨ ~><~ (≻1 (max-≤l _ _) p) p ⟩
      (c ↤ a)x                                ∎
      where
      i j k : Nat
      i = fst (isupp x)
      p : i ≻ x
      p = snd (isupp x)
      j = fst (isupp ((i ~> c)((i <~ a)x)))
      q : j ≻ (i ~> c)((i <~ a)x)
      q = snd (isupp ((i ~> c)((i <~ a)x)))
      k = max i j
      A : Finset 𝔸
      A = Иe₁ (asupp x) -- atom-supports x
      s : (A -[ a ]) ∪ [ c ] atom-supports (k ~> c)((k <~ a)x)
      s = ~>atom-supports (<~atom-supports λ a' p' →
        Иe₂ (asupp ⦃ L ⦄ x) a' ⦃ p' ⦄)
      r : a # (k ~> c)((k <~ a)x)
      r = s a (∉∪ (∉-minus A) (∉∷ auto tt))

    rn₃ : -- Equation (25)
      {a b c : 𝔸}
      → -----------------------------------
      (c ↤ b)((b ↤ a)x) ≡ (c ↤ a)((c ↤ b)x)
    rn₃ {a} {b} {c} =
      (c ↤ b)((b ↤ a)x)                         ≡⟨⟩
      (j ~> c)((j <~ b)((i ~> b)((i <~ a)x)))   ≡⟨ ~><~ q (≻1 (≤-trans (max-≤r i _) (max-≤l _ _)) q) ⟩
      (k ~> c)((k <~ b)((i ~> b)((i <~ a)x)))   ≡⟨ ap ((k ~> c) ∘ (k <~ b))
                                                   (~><~ p (≻1 (≤-trans (max-≤l i _) (max-≤l _ _)) p)) ⟩
      (k ~> c)((k <~ b)((k ~> b)((k <~ a)x)))   ≡⟨ ap (k ~> c) (oc₉ _ _ _ _ _) ⟩
      (k ~> c)((k <~ a)((k ~> a)((k <~ b)x)))   ≡˘⟨ oc₈ _ _ _ _ _ ⟩
      (k ~> c)((k <~ a)((k ~> c)((k <~ b)x)))   ≡⟨ ap ((k ~> c) ∘ (k <~ a))
                                                   (~><~ (≻1 (≤-trans (max-≤l _ _) (max-≤l _ _)) p) p) ⟩
      (k ~> c)((k <~ a)((i ~> c)((i <~ b)x)))   ≡⟨ ~><~ (≻1 (max-≤r _ _) q') q' ⟩
      (j' ~> c)((j' <~ a)((i ~> c)((i <~ b)x))) ≡⟨⟩
      (c ↤ a)((c ↤ b)x)                         ∎
      where
      i j j' k : Nat
      i = fst (isupp x)
      p : i ≻ x
      p = snd (isupp x)
      j = fst (isupp ((i ~> b)((i <~ a)x)))
      q : j ≻ (i ~> b)((i <~ a)x)
      q = snd (isupp ((i ~> b)((i <~ a)x)))
      j' = fst (isupp ((i ~> c)((i <~ b)x)))
      q' : j' ≻ (i ~> c)((i <~ b)x)
      q' = snd (isupp ((i ~> c)((i <~ b)x)))
      k = max (max i j) j'

    rn₄ : -- Equation (26)
      {a b a' b' : 𝔸}
      ⦃ _ : b  ≠ a' ⦄
      ⦃ _ : a  ≠ a' ⦄
      ⦃ _ : b' ≠ a  ⦄
      → ---------------------------------------
      (b ↤ a)((b' ↤ a')x) ≡ (b' ↤ a')((b ↤ a)x)
    rn₄ {a} {b} {a'} {b'} =
      (b ↤ a)((b' ↤ a')x)                         ≡⟨⟩
      (j' ~> b)((j' <~ a)((i ~> b')((i <~ a')x))) ≡⟨ ~><~ q' (≻1 (max-≤r _ _) q') ⟩
      (k' ~> b)((k' <~ a)((i ~> b')((i <~ a')x))) ≡⟨ ap ((k' ~> b) ∘ (k' <~ a)) (~><~ p (≻1 (max-≤l _ _) p)) ⟩
      (k' ~> b)((k' <~ a)((k ~> b')((k <~ a')x))) ≡˘⟨ ap (k' ~> b) (oc₇ _ _ _ _ _ ⦃ sym≠ k' k k'≠k ⦄) ⟩
      (k' ~> b)((k ~> b')((k' <~ a)((k <~ a')x))) ≡⟨ oc₅ _ _ _ _ _ ⦃ k'≠k ⦄ ⟩
      (k ~> b')((k' ~> b)((k' <~ a)((k <~ a')x))) ≡⟨ ap ((k ~> b') ∘ (k' ~> b)) (oc₆ _ _ _ _ _) ⟩
      (k ~> b')((k' ~> b)((k <~ a')((k' <~ a)x))) ≡⟨ ap (k ~> b') (oc₇ _ _ _ _ _ ⦃ k'≠k ⦄) ⟩
      (k ~> b')((k <~ a')((k' ~> b)((k' <~ a)x))) ≡⟨ ap ((k ~> b') ∘ (k <~ a')) (~><~ (≻1 i≤k' p) p) ⟩
      (k ~> b')((k <~ a')((i ~> b)((i <~ a)x)))   ≡⟨ ~><~ (≻1 (max-≤r _ _) q) q ⟩
      (j ~> b')((j <~ a')((i ~> b)((i <~ a)x)))   ≡⟨⟩
      (b' ↤ a')((b ↤ a)x)                         ∎
      where
      i j j' k k' : Nat
      i = fst (isupp x)
      p : i ≻ x
      p = snd (isupp x)
      j = fst (isupp ((i ~> b)((i <~ a)x)))
      q : j ≻ (i ~> b)((i <~ a)x)
      q = snd (isupp ((i ~> b)((i <~ a)x)))
      j' = fst (isupp ((i ~> b')((i <~ a')x)))
      q' : j' ≻ (i ~> b')((i <~ a')x)
      q' = snd (isupp ((i ~> b')((i <~ a')x)))
      k = max i j
      k' = max (suc k) j'
      i≤k' : i ≤ k'
      i≤k' = ≤-trans (max-≤l _ j) (≤-trans auto (max-≤l _ j'))
      k'≠k : k' ≠ k
      k'≠k = ¬≡→≠ (<-not-equal (max-≤l _ j') ∘ sym)

----------------------------------------------------------------------
-- Freshness for rensets ⟨Lemma 2.18, Corollary 2.19⟩
----------------------------------------------------------------------
module _
  {X : Type}
  ⦃ _ : lns X ⦄
  {x : X}
  {a : 𝔸}
  where
  abstract
    #→ren# : -- Equation (28), first implication
      (_ : a # x)
      (b : 𝔸)
      → ----------
      (b ↤ a)x ≡ x
    #→ren# a#x b =
      (b ↤ a) x           ≡⟨⟩
      (i ~> b)((i <~ a)x) ≡⟨ ap (i ~> b) (#2 a#x) ⟩
      (i ~> b)x           ≡⟨ ≻3 p ≤-refl ⟩
      x                   ∎
      where
      i : Nat
      i = fst (isupp x)
      p : i ≻ x
      p = snd (isupp x)

    ∀→И : -- Equation (28), second implication
      (∀ b → (b ↤ a)x ≡ x)
      → --------------------
      И[ b ∈ 𝔸 ] (b ↤ a)x ≡ x
    ∀→И p = Иi Ø λ b → p b

    ren#→# : -- Equation (28), third implication
      (_ : И[ b ∈ 𝔸 ] (b ↤ a)x ≡ x)
      → ---------------------------
      a # x
    ren#→# p = #3 {a = a}{x}{i}
      ((i <~ a) x                    ≡˘⟨ ap (i <~ a) (≻3 q ≤-refl) ⟩
       (i <~ a)((i ~> a)x)           ≡˘⟨ ap ((i <~ a) ∘ (i ~> a)) (#2 b#x) ⟩
       (i <~ a)((i ~> a)((i <~ b)x)) ≡⟨ oc₉ _ _ _ _ _ ⟩
       (i <~ b)((i ~> b)((i <~ a)x)) ≡⟨ ap (i <~ b) (Иe₂ p b ⦃ b∉A ⦄) ⟩
       (i <~ b)x                     ≡⟨ #2 b#x ⟩
       x                             ∎)
      where
      A : Finset 𝔸
      A = Иe₁ p
      b : 𝔸
      b = new (A ∪ Иe₁ (asupp x))
      b#x : b # x
      b#x = Иe₂ (asupp x) b ⦃ ∉∪₂ (Иe₁ p) (unfinite (A ∪ Иe₁ (asupp x))) ⦄
      b∉A : b ∉ A
      b∉A = ∉∪₁ (unfinite (A ∪ Иe₁ (asupp x)))
      i : Nat
      i = fst (isupp x)
      q : i ≻ x
      q = snd (isupp x)

#↤ : -- Corollary 2.19
  {X : Type}
  ⦃ _ : lns X ⦄
  (x : X)
  (a b c : 𝔸)
  ⦃ _ : c # x ⦄
  ⦃ _ : c ≠ b ⦄
  → -----------
  c # (b ↤ a)x
#↤ x a b c with b ≡? a
... | yes b≡a = ap (0 <~ c) b↤ax≡x ∙ auto ∙ sym b↤ax≡x
  where b↤ax≡x = ap (λ b → (b ↤ a)x) b≡a ∙ rn₁
... | no b≠a = ren#→# {x = (b ↤ a)x} {c} (Иi [ a ] и₂)
  where
  и₂ :
    (d : 𝔸)
    ⦃ _ : d ∉ [ a ] ⦄
    → ----------------------------
    (d ↤ c)((b ↤ a) x) ≡ (b ↤ a) x
  и₂ d with c ≡? a
  ... | yes c≡a = ap (λ c → (d ↤ c)((b ↤ a) x)) c≡a ∙ rn₂ ⦃ auto ⦄ ⦃ ¬≡→≠ (b≠a ∘ sym) ⦄
  ... | no g =
    (d ↤ c)((b ↤ a) x) ≡⟨ rn₄ {a = c} {d} {a} {b} ⦃ ∉∷₁ auto ⦄ ⦃ ¬≡→≠ g ⦄ ⦃ sym≠ c b auto ⦄ ⟩
    (b ↤ a)((d ↤ c) x) ≡⟨ ap (b ↤ a) (#→ren# auto d) ⟩
    (b ↤ a) x          ∎

#↤' :
  {X : Type}
  ⦃ _ : lns X ⦄
  (x : X)
  (a b : 𝔸)
  ⦃ _ : a ≠ b ⦄
  → -----------
  a # (b ↤ a)x
#↤' x a b = ren#→# (Иi Ø λ _ → rn₂)

ren-supp : -- Remark 2.20
  {X : Type}
  ⦃ _ : lns X ⦄
  (x : X)
  → ------------------------------
  И[ a ∈ 𝔸 ] И[ b ∈ 𝔸 ] (b ↤ a)x ≡ x
ren-supp x =
  Иi (Иe₁ (asupp x)) λ a → Иi Ø λ b → #→ren# (Иe₂ (asupp x) a) b

----------------------------------------------------------------------
-- Name-name swapping ⟨Equation (29)⟩
----------------------------------------------------------------------
module _ {X : Type}⦃ _ : lns X ⦄ where
  abstract
    infix 5 _≀ₐₐ_
    _≀ₐₐ_ : {X : Type}⦃ _ : lns X ⦄ → 𝔸 → 𝔸 → X → X
    (a ≀ₐₐ b)x =
      let c = new ([ a ] ∪ [ b ] ∪ Иe₁ (asupp x)) in
      (b ↤ c)((a ↤ b)((c ↤ a)x))

    ≀ₐₐwelldef :
      (a b c c' : 𝔸)
      (x : X)
      ⦃ _ : c # x ⦄
      ⦃ _ : c ≠ a ⦄
      ⦃ _ : c ≠ b ⦄
      ⦃ _ : c' # x ⦄
      ⦃ _ : c' ≠ a ⦄
      ⦃ _ : c' ≠ b ⦄
      → --------------------------
      (b ↤ c)((a ↤ b)((c ↤ a)x)) ≡
      (b ↤ c')((a ↤ b)((c' ↤ a)x))
    ≀ₐₐwelldef a b c c' x with c' ≡? c
    ... | yes c'≡c = ap (λ c → (b ↤ c)((a ↤ b)((c ↤ a)x))) (sym c'≡c)
    ... | no f =
      (b ↤ c)((a ↤ b)((c ↤ a)x))             ≡˘⟨ ap (b ↤ c) (#→ren# (#↤ ((c ↤ a)x) b a c'
                                                             ⦃ #↤ x a c c' ⦃ auto ⦄ ⦃ ¬≡→≠ f ⦄ ⦄) b) ⟩
      (b ↤ c)((b ↤ c')((a ↤ b)((c ↤ a)x)))   ≡˘⟨ rn₃ ⟩
      (b ↤ c')((c' ↤ c)((a ↤ b)((c ↤ a)x)))  ≡⟨ ap (b ↤ c') (rn₄ {a = c} ⦃ auto ⦄ ⦃ auto ⦄ ⦃ sym≠ c a auto ⦄) ⟩
      (b ↤ c')((a ↤ b)((c' ↤ c)((c ↤ a)x)))  ≡⟨ ap ((b ↤ c') ∘ (a ↤ b)) rn₃ ⟩
      (b ↤ c')((a ↤ b)((c' ↤ a)((c' ↤ c)x))) ≡⟨ ap ((b ↤ c') ∘ (a ↤ b) ∘ (c' ↤ a)) (#→ren# auto c') ⟩
      (b ↤ c')((a ↤ b)((c' ↤ a)x))           ∎

    ≀ₐₐfresh :
      (a b c : 𝔸)
      (x : X)
      ⦃ _ : c # x ⦄
      ⦃ _ : c ≠ a ⦄
      ⦃ _ : c ≠ b ⦄
      → -------------------------------------
      (a ≀ₐₐ b)x ≡ (b ↤ c)((a ↤ b)((c ↤ a)x))
    ≀ₐₐfresh a b c x =
      let
        as = [ a ] ∪ [ b ] ∪ Иe₁ (asupp x)
        d = new as
        instance
          _ : d # x
          _ = Иe₂ (asupp x) d ⦃ ∉∷₂ (∉∷₂ (unfinite as)) ⦄
          _ : d ≠ a
          _ = ∉∷₁ (unfinite as)
          _ : d ≠ b
          _ = ∉∷₁ (∉∷₂ (unfinite as))
      in ≀ₐₐwelldef a b d c x

  #≀ₐₐ :
    (a b c : 𝔸)
    (x : X)
    ⦃ _ : c # x ⦄
    ⦃ _ : c ≠ a ⦄
    ⦃ _ : c ≠ b ⦄
    → ------------
    c # (a ≀ₐₐ b)x
  #≀ₐₐ a b c x = subst (c #_) (sym $ ≀ₐₐfresh a b c x) (#↤' _ c b)

  -- Alternative definition of name-name swapping ⟨Equation (30)⟩
  alt-≀ₐₐ :
    (a b : 𝔸)
    (i j : Nat)
    (x : X)
    (_ : i ≻ x)
    (_ : j ≻ x)
    ⦃ _ : i ≠ j ⦄
    → --------------------------------------------------
    (a ≀ₐₐ b)x ≡ (j ~> a)((i ~> b)((j <~ b)((i <~ a)x)))
  alt-≀ₐₐ a b i j x p q =
    let
      cs = [ a ] ∪ [ b ] ∪ Иe₁ (asupp x)
      c  = new cs
      r : i ≻ (a ↤ b)((c ↤ a)x)
      r = ≻↤ _ _ _ _ (≻↤ _ _ _ _ p)
      s : j ≻ (c ↤ a)x
      s = ≻↤ _ _ _ _ q
      instance
        _ : j ≠ i
        _ = sym≠ i j auto
        _ : c # x
        _ = Иe₂ (asupp x) c ⦃ ∉∷₂ (∉∷₂ (unfinite cs)) ⦄
        _ : c ≠ b
        _ = ∉∷₁ (∉∷₂ (unfinite cs))
        _ : c ≠ a
        _ = ∉∷₁ (unfinite cs)
        _ : a ≠ c
        _ = sym≠ c a auto
        _ : c # (j <~ b)((i <~ a)x)
        _ = #<~ _ _ _ _ ⦃ #<~ _ _ _ _ ⦄
    in
      (a ≀ₐₐ b)x                                                  ≡⟨ ≀ₐₐfresh a b c x ⟩
      (b ↤ c)((a ↤ b)((c ↤ a)x))                                  ≡⟨ ↤fresh _ _ r ⟩
      (i ~> b)((i <~ c)((a ↤ b)((c ↤ a)x)))                       ≡⟨ ap ((i ~> b) ∘ (i <~ c)) (↤fresh _ _ s) ⟩
      (i ~> b)((i <~ c)((j ~> a)((j <~ b)((c ↤ a)x))))            ≡⟨ ap ((i ~> b) ∘ (i <~ c) ∘ (j ~> a) ∘ (j <~ b)) (↤fresh _ _ p) ⟩
      (i ~> b)((i <~ c)((j ~> a)((j <~ b)((i ~> c)((i <~ a)x))))) ≡˘⟨ ap ((i ~> b) ∘ (i <~ c) ∘ (j ~> a)) (oc₇ _ _ _ _ _) ⟩
      (i ~> b)((i <~ c)((j ~> a)((i ~> c)((j <~ b)((i <~ a)x))))) ≡˘⟨ ap (i ~> b) (oc₇ _ _ _ _ _) ⟩
      (i ~> b)((j ~> a)((i <~ c)((i ~> c)((j <~ b)((i <~ a)x))))) ≡⟨ oc₅ _ _ _ _ _ ⟩
      (j ~> a)((i ~> b)((i <~ c)((i ~> c)((j <~ b)((i <~ a)x))))) ≡⟨ ap ((j ~> a) ∘ (i ~> b)) (oc₃ _ _ _) ⟩
      (j ~> a)((i ~> b)((i <~ c)((j <~ b)((i <~ a)x))))           ≡⟨ ap ((j ~> a) ∘ (i ~> b)) (#2 auto) ⟩
      (j ~> a)((i ~> b)((j <~ b)((i <~ a)x)))                     ∎

--   --------------------------------------------------------------------
  -- Properties of name-swapping and renaming ⟨Lemma 2.21⟩
  --------------------------------------------------------------------
  ts₁ : -- Equation (31)
    {x : X}
    {a : 𝔸}
    → ------------
    (a ≀ₐₐ a)x ≡ x
  ts₁ {x} {a} =
    let
      as = [ a ] ∪ Иe₁ (asupp x)
      c = new as
      instance
        _ : c # x
        _ = Иe₂ (asupp x) c ⦃ ∉∷₂ (unfinite as) ⦄
        _ : c ≠ a
        _ = ∉∷₁ (unfinite as)
    in
    (a ≀ₐₐ a) x                ≡⟨ ≀ₐₐfresh a a c x ⟩
    (a ↤ c)((a ↤ a)((c ↤ a)x)) ≡⟨ ap (a ↤ c) rn₁ ⟩
    (a ↤ c)((c ↤ a)x)          ≡⟨ rn₃ ⟩
    (a ↤ a)((a ↤ c)x)          ≡⟨ rn₁ ⟩
    (a ↤ c)x                   ≡⟨ #→ren# auto a ⟩
    x                          ∎

  ts₂ : -- Equation (32 left equality)
    {x : X}
    {a b : 𝔸}
    → -----------------------
    (a ≀ₐₐ b)((a ≀ₐₐ b)x) ≡ x
  ts₂ {x} {a} {b} with a ≡? b
  ... | yes a≡b = ap (λ a → (a ≀ₐₐ b) ((a ≀ₐₐ b) x)) a≡b ∙ ts₁ ∙ ts₁
  ... | no f =
    let
      as = [ a ] ∪ [ b ] ∪ Иe₁ (asupp x)
      c = new as
      as' = [ c ] ∪ as
      c' = new as'
      instance
        _ : c' # x
        _ = Иe₂ (asupp x) c' ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (unfinite as'))) ⦄
        _ : c' ≠ a
        _ = ∉∷₁ (∉∷₂ (unfinite as'))
        _ : c' ≠ b
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (unfinite as')))
        _ : c' # (a ≀ₐₐ b)x
        _ = #≀ₐₐ a b c' x
        _ : c' ≠ c
        _ = ∉∷₁ (unfinite as')
        _ : a ≠ c
        _ = sym≠ c a (∉∷₁ (unfinite as))
        _ : b ≠ a
        _ = sym≠ a b (¬≡→≠ f)
        _ : b ≠ c
        _ = sym≠ c b (∉∷₁ (∉∷₂ (unfinite as)))
        _ : c # x
        _ = Иe₂ (asupp x) c ⦃ ∉∷₂ (∉∷₂ (unfinite as)) ⦄
    in
    (a ≀ₐₐ b)((a ≀ₐₐ b)x)                                    ≡⟨ ≀ₐₐfresh a b c' ((a ≀ₐₐ b)x) ⟩
    (b ↤ c')((a ↤ b)((c' ↤ a)((a ≀ₐₐ b)x)))                  ≡⟨ ap ((b ↤ c') ∘ (a ↤ b) ∘ (c' ↤ a))
                                                                (≀ₐₐfresh a b c x ⦃ auto ⦄ ⦃ sym≠ _ _ auto ⦄ ⦃ sym≠ _ _ auto ⦄) ⟩
    (b ↤ c')((a ↤ b)((c' ↤ a)((b ↤ c)((a ↤ b)((c ↤ a)x)))))  ≡⟨ ap ((b ↤ c') ∘ (a ↤ b)) (rn₄ {a = a} {c'} {c} {b}) ⟩
    (b ↤ c')((a ↤ b)((b ↤ c)((c' ↤ a)((a ↤ b)((c ↤ a)x)))))  ≡⟨ ap ((b ↤ c') ∘ (a ↤ b) ∘ (b ↤ c)) rn₃ ⟩
    (b ↤ c')((a ↤ b)((b ↤ c)((c' ↤ b)((c' ↤ a)((c ↤ a)x))))) ≡⟨ ap ((b ↤ c') ∘ (a ↤ b) ∘ (b ↤ c) ∘ (c' ↤ b))
                                                                (rn₂ {a = a}{c'}{c}) ⟩
    (b ↤ c')((a ↤ b)((b ↤ c)((c' ↤ b)((c ↤ a)x))))           ≡⟨ ap (b ↤ c') rn₃ ⟩
    (b ↤ c')((a ↤ c)((a ↤ b)((c' ↤ b)((c ↤ a)x))))           ≡⟨ ap ((b ↤ c') ∘ (a ↤ c))
                                                                (rn₂ {a = b}{a}{c'} ⦃ sym≠ c' b auto ⦄) ⟩
    (b ↤ c')((a ↤ c)((c' ↤ b)((c ↤ a)x)))                    ≡⟨ rn₄ {a = c'} {b} {c} {a} ⦃ auto ⦄ ⦃ auto ⦄ ⦃ sym≠ c' a auto ⦄ ⟩
    (a ↤ c)((b ↤ c')((c' ↤ b)((c ↤ a)x)))                    ≡⟨ ap (a ↤ c) rn₃ ⟩
    (a ↤ c)((b ↤ b)((b ↤ c')((c ↤ a)x)))                     ≡⟨ ap (a ↤ c) rn₁ ⟩
    (a ↤ c)((b ↤ c')((c ↤ a)x))                              ≡⟨ rn₄ {a = c} {a} {c'} {b} ⦃ sym≠ c' a auto ⦄ ⦃ sym≠ c' c auto ⦄ ⟩
    (b ↤ c')((a ↤ c)((c ↤ a)x))                              ≡⟨ ap (b ↤ c') rn₃ ⟩
    (b ↤ c')((a ↤ a)((a ↤ c)x))                              ≡⟨ ap (b ↤ c') rn₁ ⟩
    (b ↤ c')((a ↤ c)x)                                       ≡⟨ ap (b ↤ c') (#→ren# auto a) ⟩
    (b ↤ c')x                                                ≡⟨ #→ren# auto b ⟩
    x                                                        ∎

  ts₂' : -- Equation (32 right equality)
    {x : X}
    {a b : 𝔸}
    → -----------------------
    (a ≀ₐₐ b)((b ≀ₐₐ a)x) ≡ x
  ts₂' {x} {a} {b} with a ≡? b
  ... | yes a≡b = ap (λ a → (a ≀ₐₐ b) ((b ≀ₐₐ a) x)) a≡b ∙ ts₁ ∙ ts₁
  ... | no f =
    let
      as = [ b ] ∪ [ a ] ∪ Иe₁ (asupp x)
      c = new as
      as' = [ c ] ∪ as
      c' = new as'
      instance
        _ : c' # x
        _ = Иe₂ (asupp x) c' ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (unfinite as'))) ⦄
        _ : c' ≠ b
        _ = ∉∷₁ (∉∷₂ (unfinite as'))
        _ : c' ≠ a
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (unfinite as')))
        _ : c' # (b ≀ₐₐ a)x
        _ = #≀ₐₐ b a c' x
        _ : c' ≠ c
        _ = ∉∷₁ (unfinite as')
        _ : b ≠ c
        _ = sym≠ c b (∉∷₁ (unfinite as))
        _ : a ≠ b
        _ = ¬≡→≠ f
        _ : a ≠ c
        _ = sym≠ c a (∉∷₁ (∉∷₂ (unfinite as)))
        _ : c # x
        _ = Иe₂ (asupp x) c ⦃ ∉∷₂ (∉∷₂ (unfinite as)) ⦄
    in
    (a ≀ₐₐ b)((b ≀ₐₐ a)x)                                    ≡⟨ ≀ₐₐfresh a b c' ((b ≀ₐₐ a)x) ⟩
    (b ↤ c')((a ↤ b)((c' ↤ a)((b ≀ₐₐ a)x)))                  ≡⟨ ap ((b ↤ c') ∘ (a ↤ b) ∘ (c' ↤ a))
                                                                (≀ₐₐfresh b a c x ⦃ auto ⦄ ⦃ sym≠ _ _ auto ⦄ ⦃ sym≠ _ _ auto ⦄) ⟩
    (b ↤ c')((a ↤ b)((c' ↤ a)((a ↤ c)((b ↤ a)((c ↤ b)x)))))  ≡⟨ ap ((b ↤ c') ∘ (a ↤ b)) rn₃ ⟩
    (b ↤ c')((a ↤ b)((c' ↤ c)((c' ↤ a)((b ↤ a)((c ↤ b)x))))) ≡⟨ ap (b ↤ c') (rn₄ {a = b} {a} {c} {c'}) ⟩
    (b ↤ c')((c' ↤ c)((a ↤ b)((c' ↤ a)((b ↤ a)((c ↤ b)x))))) ≡⟨ ap ((b ↤ c') ∘ (c' ↤ c) ∘ (a ↤ b)) (rn₂ {a = a} {c'} {b}) ⟩
    (b ↤ c')((c' ↤ c)((a ↤ b)((b ↤ a)((c ↤ b)x))))           ≡⟨ ap ((b ↤ c') ∘ (c' ↤ c)) rn₃ ⟩
    (b ↤ c')((c' ↤ c)((a ↤ a)((a ↤ b)((c ↤ b)x))))           ≡⟨ ap ((b ↤ c') ∘ (c' ↤ c)) rn₁ ⟩
    (b ↤ c')((c' ↤ c)((a ↤ b)((c ↤ b)x)))                    ≡⟨ ap ((b ↤ c') ∘ (c' ↤ c)) (rn₂ {a = b} {a} {c}) ⟩
    (b ↤ c')((c' ↤ c)((c ↤ b)x))                             ≡⟨ ap (b ↤ c') rn₃ ⟩
    (b ↤ c')((c' ↤ b)((c' ↤ c)x))                            ≡⟨ rn₃ ⟩
    (b ↤ b)((b ↤ c')((c' ↤ c)x))                             ≡⟨ rn₁ ⟩
    (b ↤ c')((c' ↤ c)x)                                      ≡⟨ ap (b ↤ c') (#→ren# auto c') ⟩
    (b ↤ c')x                                                ≡⟨ #→ren# auto b ⟩
    x                                                        ∎

  ts₃ : -- Equation (33)
    {x : X}
    {a b c d : 𝔸}
    ⦃ _ : b ≠ c ⦄
    ⦃ _ : c ≠ a ⦄
    ⦃ _ : a ≠ d ⦄
    ⦃ _ : d ≠ b ⦄
    → -------------------------------------------
    (a ≀ₐₐ b)((c ≀ₐₐ d)x) ≡ (c ≀ₐₐ d)((a ≀ₐₐ b)x)
  ts₃ {x} {a} {b} {c} {d} =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ [ d ] ∪ Иe₁ (asupp x)
      e = new as
      as' = [ e ] ∪ as
      e' = new as'
      instance
        _ : e # x
        _ = Иe₂ (asupp x) e ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (∉∷₂ (unfinite as)))) ⦄
        _ : e ≠ a
        _ = ∉∷₁ (unfinite as)
        _ : e ≠ b
        _ = ∉∷₁ (∉∷₂ (unfinite as))
        _ : e ≠ c
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (unfinite as)))
        _ : e ≠ d
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (∉∷₂ (unfinite as))))
        _ : e # (c ≀ₐₐ d)x
        _ = #≀ₐₐ c d e x
        _ : e' # x
        _ = Иe₂ (asupp x) e' ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (∉∷₂ (∉∷₂ (unfinite as'))))) ⦄
        _ : e' ≠ a
        _ = ∉∷₁ (∉∷₂ (unfinite as'))
        _ : e' ≠ b
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (unfinite as')))
        _ : e' ≠ c
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (∉∷₂ (unfinite as'))))
        _ : e' ≠ d
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (∉∷₂ (∉∷₂ (unfinite as')))))
        _ : e' # (a ≀ₐₐ b)x
        _ = #≀ₐₐ a b e' x
        _ : e ≠ e'
        _ = sym≠ e' e (∉∷₁ (unfinite as'))
        _ : a ≠ e'
        _ = sym≠ e' a auto
        _ : d ≠ a
        _ = sym≠ a d auto
        _ : b ≠ e'
        _ = sym≠ e' b auto
        _ : d ≠ e
        _ = sym≠ e d auto
        _ : b ≠ d
        _ = sym≠ d b auto
        _ : c ≠ b
        _ = sym≠ b c auto
        _ : c ≠ e
        _ = sym≠ e c auto
        _ : a ≠ c
        _ = sym≠ c a auto
        _ : e' ≠ e
        _ = sym≠ e e' auto
    in
    (a ≀ₐₐ b)((c ≀ₐₐ d)x)                                   ≡⟨ ≀ₐₐfresh a b e ((c ≀ₐₐ d)x) ⟩
    (b ↤ e)((a ↤ b)((e ↤ a)((c ≀ₐₐ d)x)))                   ≡⟨ ap ((b ↤ e) ∘ (a ↤ b) ∘ (e ↤ a)) (≀ₐₐfresh c d e' x) ⟩
    (b ↤ e)((a ↤ b)((e ↤ a)((d ↤ e')((c ↤ d)((e' ↤ c)x))))) ≡⟨ ap ((b ↤ e) ∘ (a ↤ b)) (rn₄ {a = a} {e} {e'} {d}) ⟩
    (b ↤ e)((a ↤ b)((d ↤ e')((e ↤ a)((c ↤ d)((e' ↤ c)x))))) ≡⟨ ap (b ↤ e) (rn₄ {a = b} {a} {e'} {d} ) ⟩
    (b ↤ e)((d ↤ e')((a ↤ b)((e ↤ a)((c ↤ d)((e' ↤ c)x))))) ≡⟨ rn₄ {a = e} {b} {e'} {d} ⟩
    (d ↤ e')((b ↤ e)((a ↤ b)((e ↤ a)((c ↤ d)((e' ↤ c)x))))) ≡⟨ ap ((d ↤ e') ∘ (b ↤ e) ∘ (a ↤ b)) (rn₄ {a = a} {e} {d} {c}) ⟩
    (d ↤ e')((b ↤ e)((a ↤ b)((c ↤ d)((e ↤ a)((e' ↤ c)x))))) ≡⟨ ap ((d ↤ e') ∘ (b ↤ e)) (rn₄ {a = b} {a} {d} {c}) ⟩
    (d ↤ e')((b ↤ e)((c ↤ d)((a ↤ b)((e ↤ a)((e' ↤ c)x))))) ≡⟨ ap (d ↤ e') (rn₄ {a = e} {b} {d} {c}) ⟩
    (d ↤ e')((c ↤ d)((b ↤ e)((a ↤ b)((e ↤ a)((e' ↤ c)x))))) ≡⟨ ap ((d ↤ e') ∘ (c ↤ d) ∘ (b ↤ e) ∘ (a ↤ b)) (rn₄ {a = a} {e} {c} {e'}) ⟩
    (d ↤ e')((c ↤ d)((b ↤ e)((a ↤ b)((e' ↤ c)((e ↤ a)x))))) ≡⟨ ap ((d ↤ e') ∘ (c ↤ d) ∘ (b ↤ e)) (rn₄ {a = b} {a} {c} {e'}) ⟩
    (d ↤ e')((c ↤ d)((b ↤ e)((e' ↤ c)((a ↤ b)((e ↤ a)x))))) ≡⟨ ap ((d ↤ e') ∘ (c ↤ d)) (rn₄ {a = e} {b} {c} {e'}) ⟩
    (d ↤ e')((c ↤ d)((e' ↤ c)((b ↤ e)((a ↤ b)((e ↤ a)x))))) ≡˘⟨ ap ((d ↤ e') ∘ (c ↤ d) ∘ (e' ↤ c)) (≀ₐₐfresh a b e x) ⟩
    (d ↤ e')((c ↤ d)((e' ↤ c)((a ≀ₐₐ b)x)))                 ≡˘⟨ ≀ₐₐfresh c d e' ((a ≀ₐₐ b)x) ⟩
    (c ≀ₐₐ d)((a ≀ₐₐ b)x)                                   ∎

  ts₄ : -- Equation (34)
    {x : X}
    {a b c : 𝔸}
    ⦃ _ : b ≠ c ⦄
    ⦃ _ : c ≠ a ⦄
    → -------------------------------------------
    (a ≀ₐₐ b)((c ≀ₐₐ a)x) ≡ (c ≀ₐₐ b)((a ≀ₐₐ b)x)
  ts₄ {x} {a} {b} {c} with b ≡? a
  ... | yes b≡a =
    (a ≀ₐₐ b)((c ≀ₐₐ a)x) ≡⟨ ap (λ a → (a ≀ₐₐ b)((c ≀ₐₐ a)x)) (sym b≡a) ⟩
    (b ≀ₐₐ b)((c ≀ₐₐ b)x) ≡⟨ ts₁ ∙ ap (c ≀ₐₐ b) (sym ts₁) ⟩
    (c ≀ₐₐ b)((b ≀ₐₐ b)x) ≡⟨ ap (λ b₀ → (c ≀ₐₐ b)((b₀ ≀ₐₐ b)x)) b≡a ⟩
    (c ≀ₐₐ b)((a ≀ₐₐ b)x) ∎
  ... | no f =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (asupp x)
      e = new as
      as' = [ e ] ∪ as
      e' = new as'
      instance
        _ : e # x
        _ = Иe₂ (asupp x) e ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (unfinite as))) ⦄
        _ : e ≠ a
        _ = ∉∷₁ (unfinite as)
        _ : e ≠ b
        _ = ∉∷₁ (∉∷₂ (unfinite as))
        _ : e ≠ c
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (unfinite as)))
        _ : e # (c ≀ₐₐ a)x
        _ = #≀ₐₐ c a e x
        _ : e' # x
        _ = Иe₂ (asupp x) e' ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (∉∷₂ (unfinite as')))) ⦄
        _ : e' ≠ c
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (∉∷₂ (unfinite as'))))
        _ : e' ≠ a
        _ = ∉∷₁ (∉∷₂ (unfinite as'))
        _ : e' # x
        _ = Иe₂ (asupp x) e' ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (∉∷₂ (unfinite as')))) ⦄
        _ : e' ≠ a
        _ = ∉∷₁ (∉∷₂ (unfinite as'))
        _ : e' ≠ b
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (unfinite as')))
        _ : e # (a ≀ₐₐ b)x
        _ = #≀ₐₐ a b e x
        _ : a ≠ e'
        _ = sym≠ e' a auto
        _ : b ≠ e'
        _ = sym≠ e' b auto
        _ : a ≠ c
        _ = sym≠ c a auto
        _ : e' ≠ e
        _ = ∉∷₁ (unfinite as')
        _ : e ≠ e'
        _ = sym≠ e' e auto
        _ : c ≠ e'
        _ = sym≠ e' c auto
        _ : c ≠ b
        _ = sym≠ b c auto
        _ : b ≠ a
        _ = ¬≡→≠  f
    in
    (a ≀ₐₐ b)((c ≀ₐₐ a)x)                                   ≡⟨ ≀ₐₐfresh a b e ((c ≀ₐₐ a)x) ⟩
    (b ↤ e)((a ↤ b)((e ↤ a)((c ≀ₐₐ a)x)))                   ≡⟨ ap ((b ↤ e) ∘ (a ↤ b) ∘ (e ↤ a)) (≀ₐₐfresh c a e' x) ⟩
    (b ↤ e)((a ↤ b)((e ↤ a)((a ↤ e')((c ↤ a)((e' ↤ c)x))))) ≡⟨ ap ((b ↤ e) ∘ (a ↤ b)) rn₃ ⟩
    (b ↤ e)((a ↤ b)((e ↤ e')((e ↤ a)((c ↤ a)((e' ↤ c)x))))) ≡⟨ ap ((b ↤ e) ∘ (a ↤ b) ∘ (e ↤ e')) (rn₂ {a = a} {e} {c}) ⟩
    (b ↤ e)((a ↤ b)((e ↤ e')((c ↤ a)((e' ↤ c)x))))          ≡⟨ ap ((b ↤ e) ∘ (a ↤ b)) (rn₄ {a = e'} {e} {a} {c}) ⟩
    (b ↤ e)((a ↤ b)((c ↤ a)((e ↤ e')((e' ↤ c)x))))          ≡⟨ ap ((b ↤ e) ∘ (a ↤ b) ∘ (c ↤ a)) rn₃ ⟩
    (b ↤ e)((a ↤ b)((c ↤ a)((e ↤ c)((e ↤ e')x))))           ≡⟨ ap ((b ↤ e) ∘ (a ↤ b) ∘ (c ↤ a) ∘ (e ↤ c)) (#→ren# auto e) ⟩
    (b ↤ e)((a ↤ b)((c ↤ a)((e ↤ c)x)))                     ≡˘⟨ ap ((b ↤ e) ∘ (a ↤ b) ∘ (c ↤ a)) (#→ren# (#↤ x c e e') c) ⟩
    (b ↤ e)((a ↤ b)((c ↤ a)((c ↤ e')((e ↤ c)x))))           ≡˘⟨ ap ((b ↤ e) ∘ (a ↤ b)) rn₃ ⟩
    (b ↤ e)((a ↤ b)((c ↤ e')((e' ↤ a)((e ↤ c)x))))          ≡˘⟨ ap (b ↤ e) (rn₄ {a = e'} {c} {b} {a}) ⟩
    (b ↤ e)((c ↤ e')((a ↤ b)((e' ↤ a)((e ↤ c)x))))          ≡˘⟨ ap ((b ↤ e) ∘ (c ↤ e')) (rn₂ {a = b} {c} {a}) ⟩
    (b ↤ e)((c ↤ e')((c ↤ b)((a ↤ b)((e' ↤ a)((e ↤ c)x))))) ≡˘⟨ ap ((b ↤ e) ∘ (c ↤ e') ∘ (c ↤ b) ∘ (a ↤ b)) (rn₄ {a = c} {e} {a} {e'}) ⟩
    (b ↤ e)((c ↤ e')((c ↤ b)((a ↤ b)((e ↤ c)((e' ↤ a)x))))) ≡˘⟨ ap ((b ↤ e) ∘ (c ↤ e') ∘ (c ↤ b)) (rn₄ {a = c} {e} {b} {a}) ⟩
    (b ↤ e)((c ↤ e')((c ↤ b)((e ↤ c)((a ↤ b)((e' ↤ a)x))))) ≡˘⟨ ap (b ↤ e) rn₃ ⟩
    (b ↤ e)((c ↤ b)((b ↤ e')((e ↤ c)((a ↤ b)((e' ↤ a)x))))) ≡˘⟨ ap ((b ↤ e) ∘ (c ↤ b)) (rn₄ {a = c} {e} {e'} {b}) ⟩
    (b ↤ e)((c ↤ b)((e ↤ c)((b ↤ e')((a ↤ b)((e' ↤ a)x))))) ≡˘⟨ ap ((b ↤ e) ∘ (c ↤ b) ∘ (e ↤ c)) (≀ₐₐfresh a b e' x) ⟩
    (b ↤ e)((c ↤ b)((e ↤ c)((a ≀ₐₐ b)x)))                   ≡˘⟨ ≀ₐₐfresh c b e ((a ≀ₐₐ b)x) ⟩
    (c ≀ₐₐ b)((a ≀ₐₐ b)x)                                   ∎

  ts₅ : -- Equation (35)
    {x : X}
    {a b c : 𝔸}
    ⦃ _ : b ≠ c ⦄
    → -------------------------------------
    (c ↤ b)((a ≀ₐₐ b)x) ≡ (a ↤ b)((c ↤ a)x)
  ts₅ {x} {a} {b} {c} with b ≡? a
  ... | yes b≡a =
    (c ↤ b)((a ≀ₐₐ b)x) ≡⟨ ap (λ b → (c ↤ b)((a ≀ₐₐ b)x)) b≡a ⟩
    (c ↤ a)((a ≀ₐₐ a)x) ≡⟨ ap (c ↤ a) ts₁ ∙ sym rn₁ ⟩
    (a ↤ a)((c ↤ a)x)   ≡⟨ ap (λ a₀ → (a ↤ a₀)((c ↤ a)x)) (sym b≡a) ⟩
    (a ↤ b)((c ↤ a)x)   ∎
  ... | no f =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (asupp x)
      d = new as
      instance
        _ : d # x
        _ = Иe₂ (asupp x) d ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (unfinite as))) ⦄
        _ : d ≠ a
        _ = ∉∷₁ (unfinite as)
        _ : d ≠ b
        _ = ∉∷₁ (∉∷₂ (unfinite as))
        _ : b ≠ a
        _ = ¬≡→≠ f
        _ : c ≠ b
        _ = sym≠ b c auto
        _ : a ≠ d
        _ = sym≠ d a auto
    in
    (c ↤ b)((a ≀ₐₐ b)x)                 ≡⟨ ap (c ↤ b) (≀ₐₐfresh a b d x) ⟩
    (c ↤ b)((b ↤ d)((a ↤ b)((d ↤ a)x))) ≡⟨ rn₃  ⟩
    (c ↤ d)((c ↤ b)((a ↤ b)((d ↤ a)x))) ≡⟨ ap (c ↤ d) (rn₂ {a = b} {c} {a}) ⟩
    (c ↤ d)((a ↤ b)((d ↤ a)x))          ≡⟨ rn₄ {a = d} {c} {b} {a} ⟩
    (a ↤ b)((c ↤ d)((d ↤ a)x))          ≡⟨ ap (a ↤ b) rn₃ ⟩
    (a ↤ b)((c ↤ a)((c ↤ d)x))          ≡⟨ ap ((a ↤ b) ∘ (c ↤ a)) (#→ren# auto c) ⟩
    (a ↤ b)((c ↤ a)x)                   ∎

  ts₆ : -- Equation (36)
    {x : X}
    {a b c d : 𝔸}
    ⦃ _ : b ≠ c ⦄
    ⦃ _ : c ≠ a ⦄
    ⦃ _ : a ≠ d ⦄
    ⦃ _ : d ≠ b ⦄
    → ---------------------------------------
    (a ≀ₐₐ b)((d ↤ c)x) ≡ (d ↤ c)((a ≀ₐₐ b)x)
  ts₆ {x} {a} {b} {c} {d} =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ [ d ] ∪ Иe₁ (asupp x)
      e = new as
      instance
        _ : e # x
        _ = Иe₂ (asupp x) e ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (∉∷₂ (unfinite as)))) ⦄
        _ : e ≠ a
        _ = ∉∷₁ (unfinite as)
        _ : e ≠ b
        _ = ∉∷₁ (∉∷₂ (unfinite as))
        _ : e ≠ c
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (unfinite as)))
        _ : e ≠ d
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (∉∷₂ (unfinite as))))
        _ : e # (d ↤ c)x
        _ = #↤ x c d e
        _ : a ≠ c
        _ = sym≠ c a auto
        _ : d ≠ a
        _ = sym≠ a d auto
        _ : d ≠ e
        _ = sym≠ e d auto
    in
    (a ≀ₐₐ b)((d ↤ c)x)                 ≡⟨ ≀ₐₐfresh a b e ((d ↤ c)x) ⟩
    (b ↤ e)((a ↤ b)((e ↤ a)((d ↤ c)x))) ≡⟨ ap ((b ↤ e) ∘ (a ↤ b)) (rn₄ {a = a} {e} {c} {d}) ⟩
    (b ↤ e)((a ↤ b)((d ↤ c)((e ↤ a)x))) ≡⟨ ap (b ↤ e) (rn₄ {a = b} {a} {c} {d}) ⟩
    (b ↤ e)((d ↤ c)((a ↤ b)((e ↤ a)x))) ≡⟨ rn₄ {a = e} {b} {c} {d} ⟩
    (d ↤ c)((b ↤ e)((a ↤ b)((e ↤ a)x))) ≡˘⟨ ap (d ↤ c) (≀ₐₐfresh a b e x) ⟩
    (d ↤ c)((a ≀ₐₐ b)x)                 ∎

  ts₇ : -- Equation (37)
    {x : X}
    {a b c : 𝔸}
    ⦃ _ : b ≠ c ⦄
    ⦃ _ : c ≠ a ⦄
    → ---------------------------------------
    (a ≀ₐₐ b)((a ↤ c)x) ≡ (b ↤ c)((a ≀ₐₐ b)x)
  ts₇ {x} {a} {b} {c} =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (asupp x)
      d = new as
      instance
        _ : d # x
        _ = Иe₂ (asupp x) d ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (unfinite as))) ⦄
        _ : d ≠ a
        _ = ∉∷₁ (unfinite as)
        _ : d ≠ b
        _ = ∉∷₁ (∉∷₂ (unfinite as))
        _ : d ≠ c
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (unfinite as)))
        _ : d # (a ↤ c)x
        _ = #↤ x c a d
        _ : a ≠ c
        _ = sym≠ c a auto
    in
    (a ≀ₐₐ b)((a ↤ c)x)                 ≡⟨ ≀ₐₐfresh a b d ((a ↤ c)x) ⟩
    (b ↤ d)((a ↤ b)((d ↤ a)((a ↤ c)x))) ≡⟨ ap ((b ↤ d) ∘ (a ↤ b)) rn₃ ⟩
    (b ↤ d)((a ↤ b)((d ↤ c)((d ↤ a)x))) ≡⟨ ap (b ↤ d) (rn₄ {a = b} {a} {c} {d}) ⟩
    (b ↤ d)((d ↤ c)((a ↤ b)((d ↤ a)x))) ≡⟨ rn₃ ⟩
    (b ↤ c)((b ↤ d)((a ↤ b)((d ↤ a)x))) ≡˘⟨ ap (b ↤ c) (≀ₐₐfresh a b d x) ⟩
    (b ↤ c)((a ≀ₐₐ b)x)                 ∎

  ts₈ : -- Equation (38)
    {x : X}
    {a b c : 𝔸}
    ⦃ _ : b ≠ c ⦄
    ⦃ _ : c ≠ a ⦄
    → ---------------------------------------
    (a ≀ₐₐ b)((c ↤ a)x) ≡ (c ↤ b)((a ≀ₐₐ b)x)
  ts₈ {x} {a} {b} {c} with b ≡? a
  ... | yes b≡a =
    (a ≀ₐₐ b)((c ↤ a)x) ≡⟨ ap (λ a → (a ≀ₐₐ b)((c ↤ a)x)) (sym b≡a) ⟩
    (b ≀ₐₐ b)((c ↤ b)x) ≡⟨ ts₁ ∙ ap (c ↤ b) (sym ts₁) ⟩
    (c ↤ b)((b ≀ₐₐ b)x) ≡⟨ ap (λ b₀ → (c ↤ b)((b₀ ≀ₐₐ b)x)) b≡a ⟩
    (c ↤ b)((a ≀ₐₐ b)x) ∎
  ... | no f =
    let
      as = [ a ] ∪ [ b ] ∪ [ c ] ∪ Иe₁ (asupp x)
      d = new as
      instance
        _ : d # x
        _ = Иe₂ (asupp x) d ⦃ ∉∷₂ (∉∷₂ (∉∷₂ (unfinite as))) ⦄
        _ : d ≠ a
        _ = ∉∷₁ (unfinite as)
        _ : d ≠ b
        _ = ∉∷₁ (∉∷₂ (unfinite as))
        _ : d ≠ c
        _ = ∉∷₁ (∉∷₂ (∉∷₂ (unfinite as)))
        _ : d # (c ↤ a)x
        _ = #↤ x a c d
        _ : a ≠ c
        _ = sym≠ c a auto
        _ : d # (a ↤ b)((c ↤ a)x)
        _ = #↤ _ b a d
        _ : b ≠ a
        _ = ¬≡→≠ f
        _ : c ≠ b
        _ = sym≠ b c auto
        _ : a ≠ d
        _ = sym≠ d a auto
    in
    (a ≀ₐₐ b)((c ↤ a)x)                 ≡⟨ ≀ₐₐfresh a b d ((c ↤ a)x) ⟩
    (b ↤ d)((a ↤ b)((d ↤ a)((c ↤ a)x))) ≡⟨ ap ((b ↤ d) ∘ (a ↤ b)) (rn₂ {a = a} {d} {c}) ⟩
    (b ↤ d)((a ↤ b)((c ↤ a)x))          ≡⟨ #→ren# auto b ⟩
    (a ↤ b)((c ↤ a)x)                   ≡˘⟨ ap ((a ↤ b) ∘ (c ↤ a)) (#→ren# auto c) ⟩
    (a ↤ b)((c ↤ a)((c ↤ d)x))          ≡˘⟨ ap (a ↤ b) rn₃ ⟩
    (a ↤ b)((c ↤ d)((d ↤ a)x))          ≡˘⟨ rn₄ {a = d} {c} {b} {a} ⟩
    (c ↤ d)((a ↤ b)((d ↤ a)x))          ≡˘⟨ ap (c ↤ d) (rn₂ {a = b}{c}{a}) ⟩
    (c ↤ d)((c ↤ b)((a ↤ b)((d ↤ a)x))) ≡˘⟨ rn₃ ⟩
    (c ↤ b)((b ↤ d)((a ↤ b)((d ↤ a)x))) ≡˘⟨ ap (c ↤ b) (≀ₐₐfresh a b d x) ⟩
    (c ↤ b)((a ≀ₐₐ b)x)                 ∎

  ts₉ : -- Equation (39)
    {x : X}
    {a b : 𝔸}
    → ---------------------------------------
    (a ≀ₐₐ b)((b ↤ a)x) ≡ (a ↤ b)((a ≀ₐₐ b)x)
  ts₉ {x} {a} {b} with b ≡? a
  ... | yes b≡a =
    (a ≀ₐₐ b)((b ↤ a)x) ≡⟨ ap (λ b → (a ≀ₐₐ b)((b ↤ a)x)) b≡a ⟩
    (a ≀ₐₐ a)((a ↤ a)x) ≡⟨ ts₁ ∙ ap (a ↤ a) (sym ts₁) ⟩
    (a ↤ a)((a ≀ₐₐ a)x) ≡⟨ ap (λ a₀ → (a ↤ a₀)((a ≀ₐₐ a₀)x)) (sym b≡a) ⟩
    (a ↤ b)((a ≀ₐₐ b)x) ∎
  ... | no f =
    let
      as = [ a ] ∪ [ b ] ∪ Иe₁ (asupp x)
      c = new as
      instance
        _ : c # x
        _ = Иe₂ (asupp x) c ⦃ ∉∷₂ (∉∷₂ (unfinite as)) ⦄
        _ : c ≠ a
        _ = ∉∷₁ (unfinite as)
        _ : c ≠ b
        _ = ∉∷₁ (∉∷₂ (unfinite as))
        _ : c # (b ↤ a)x
        _ = #↤ x a b c
        _ : b ≠ a
        _ = ¬≡→≠ f
        _ : a ≠ b
        _ = sym≠ b a auto
        _ : c # (a ↤ b)x
        _ = #↤ x b a c
        _ : a ≠ c
        _ = sym≠ c a auto
    in
    (a ≀ₐₐ b)((b ↤ a)x)                 ≡⟨ ≀ₐₐfresh a b c ((b ↤ a)x) ⟩
    (b ↤ c)((a ↤ b)((c ↤ a)((b ↤ a)x))) ≡⟨ ap ((b ↤ c) ∘ (a ↤ b)) (rn₂ {a = a} {c} {b}) ⟩
    (b ↤ c)((a ↤ b)((b ↤ a)x))          ≡⟨ ap (b ↤ c) rn₃ ⟩
    (b ↤ c)((a ↤ a)((a ↤ b)x))          ≡⟨ ap (b ↤ c) rn₁ ⟩
    (b ↤ c)((a ↤ b)x)                   ≡⟨ #→ren# auto b ⟩
    (a ↤ b)x                            ≡˘⟨ ap (a ↤ b) (#→ren# auto a) ⟩
    (a ↤ b)((a ↤ c)x)                   ≡˘⟨ ap (a ↤ b) rn₁ ⟩
    (a ↤ b)((a ↤ a)((a ↤ c)x))          ≡˘⟨ ap (a ↤ b) rn₃ ⟩
    (a ↤ b)((a ↤ c)((c ↤ a)x))          ≡˘⟨ rn₄ {a = c} {a} {b} {a} ⟩
    (a ↤ c)((a ↤ b)((c ↤ a)x))          ≡˘⟨ ap (a ↤ c) (rn₂ {a = b} {a} {a}) ⟩
    (a ↤ c)((a ↤ b)((a ↤ b)((c ↤ a)x))) ≡˘⟨ rn₃ ⟩
    (a ↤ b)((b ↤ c)((a ↤ b)((c ↤ a)x))) ≡˘⟨ ap (a ↤ b) (≀ₐₐfresh a b c x) ⟩
    (a ↤ b)((a ≀ₐₐ b)x)                 ∎
