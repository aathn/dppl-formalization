--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.LocallyNameless.oc-Sets where

open import Lib.Prelude
open import Lib.Data.Dec
open import Lib.LocallyNameless.Unfinite

----------------------------------------------------------------------
-- oc-Sets [Section 2.2]
----------------------------------------------------------------------
record oc (X : Type) : Type where
  constructor mkoc
  infix 5 _~>_ _<~_
  field
    _~>_ : Nat → 𝔸 → X → X
    _<~_ : Nat → 𝔸 → X → X
    -- [Figure 1]
    oc₁ :
      (i : Nat)
      (a b : 𝔸)
      (x : X)
      → -----------------------------
      (i ~> a)((i ~> b)x) ≡ (i ~> b)x
    oc₂ :
      (i j : Nat)
      (a : 𝔸)
      (x : X)
      → -----------------------------
      (i <~ a)((j <~ a)x) ≡ (j <~ a)x
    oc₃ :
      (i : Nat)
      (a : 𝔸)
      (x : X)
      → -----------------------------
      (i <~ a)((i ~> a)x) ≡ (i <~ a)x
    oc₄ :
      (i : Nat)
      (a : 𝔸)
      (x : X)
      → -----------------------------
      (i ~> a)((i <~ a)x) ≡ (i ~> a)x
    oc₅ :
      (i j : Nat)
      (a b : 𝔸)
      (x : X)
      ⦃ _ : i ≠ j ⦄
      → ---------------------------------------
      (i ~> a)((j ~> b)x) ≡ (j ~> b)((i ~> a)x)
    oc₆ :
      (i j : Nat)
      (a b : 𝔸)
      (x : X)
      ⦃ _ : a ≠ b ⦄
      → ---------------------------------------
      (i <~ a)((j <~ b)x) ≡ (j <~ b)((i <~ a)x)
    oc₇ :
      (i j : Nat)
      (a b : 𝔸)
      (x : X)
      ⦃ _ : i ≠ j ⦄
      ⦃ _ : a ≠ b ⦄
      → ---------------------------------------
      (i ~> a)((j <~ b)x) ≡ (j <~ b)((i ~> a)x)
    oc₈ :
      (i j : Nat)
      (a b : 𝔸)
      (x : X)
      → -----------------------------------------------------------
      (i ~> b)((i <~ a)((j ~> b)x)) ≡ (j ~> b)((j <~ a)((i ~> a)x))
    oc₉ :
      (i j : Nat)
      (a b : 𝔸)
      (x : X)
      → -----------------------------------------------------------
      (j <~ a)((i ~> a)((j <~ b)x)) ≡ (j <~ b)((i ~> b)((i <~ a)x))

open oc ⦃ ... ⦄ public

{-# DISPLAY oc._~>_ _ i a = i ~> a #-}
{-# DISPLAY oc._<~_ _ i a = i <~ a #-}

----------------------------------------------------------------------
-- Example: oc-set of indices and atoms [Example 2.2]
----------------------------------------------------------------------
Nat𝔸 : Type
Nat𝔸 = Nat ⊎ 𝔸

private
  opn : Nat → 𝔸 → Nat𝔸 → Nat𝔸
  opn i a (inl j) = ifᵈ i ≡? j then inr a else inl j
  opn i a (inr b) = inr b

  cls : Nat → 𝔸 → Nat𝔸 → Nat𝔸
  cls i a (inl j) = inl j
  cls i a (inr b) = ifᵈ a ≡? b then inl i else inr b

  refl' : {A : Type} (x : A) → x ≡ x
  refl' x = refl

  ax₁ :
    (i : Nat)
    (a b : 𝔸)
    (x : Nat𝔸)
    → -----------------------------
    opn i a (opn i b x) ≡ opn i b x
  ax₁ i _ _ (inl j) with i ≡? j
  ... | no i≠j = ifᵈ-≠ i≠j
  ... | yes _ = refl
  ax₁ i _ _ (inr _) = refl

  ax₂ :
    (i j : Nat)
    (a : 𝔸)
    (x : Nat𝔸)
    → -----------------------------
    cls i a (cls j a x) ≡ cls j a x
  ax₂ _ _ _ (inl _) = refl
  ax₂ _ _ a (inr b) with a ≡? b
  ... | no a≠b = ifᵈ-≠ a≠b
  ... | yes _ = refl

  ax₃ :
    (i : Nat)
    (a : 𝔸)
    (x : Nat𝔸)
    → -----------------------------
    cls i a (opn i a x) ≡ cls i a x
  ax₃ i a (inl j) with i ≡? j
  ... | no _ = refl
  ... | yes i≡j = ifᵈ-≡ (refl' a) ∙ ap inl i≡j
  ax₃ _ _ (inr _) = refl

  ax₄ :
    (i : Nat)
    (a : 𝔸)
    (x : Nat𝔸)
    → -----------------------------
    opn i a (cls i a x) ≡ opn i a x
  ax₄ i a (inl j) = refl
  ax₄ i a (inr b) with a ≡? b
  ... | no _ = refl
  ... | yes a≡b = ifᵈ-≡ (refl' i) ∙ ap inr a≡b

  ax₅ :
    (i j : Nat)
    (a b : 𝔸)
    (x : Nat𝔸)
    ⦃ p : i ≠ j ⦄
    → ---------------------------------------
    opn i a (opn j b x) ≡ opn j b (opn i a x)
  ax₅ _ j _ _ (inl k)         with j ≡? k
  ax₅ i _ _ _ (inl k)         | no _ with i ≡? k
  ax₅ _ j _ _ (inl k)         | no j≠k | no _ = sym $ ifᵈ-≠ j≠k ∙ refl
  ax₅ _ _ _ _ (inl _)         | no _ | yes _ = refl
  ax₅ i j _ b (inl k) ⦃ i≠j ⦄ | yes j≡k =
    sym $ ap (opn j b) (ifᵈ-≠ i≠k) ∙ ifᵈ-≡ j≡k
    where i≠k = λ H≡ → is-no-false i≠j (H≡ ∙ sym j≡k)
  ax₅ _ _ _ _ (inr _) = refl

  ax₆ :
    (i j : Nat)
    (a b : 𝔸)
    (x : Nat𝔸)
    ⦃ p : a ≠ b ⦄
    → ---------------------------------------
    cls i a (cls j b x) ≡ cls j b (cls i a x)
  ax₆ _ _ _ _ (inl _)                     = refl
  ax₆ _ _ _ b (inr c)         with  b ≡? c
  ax₆ _ _ a _ (inr c)         | no _ with a ≡? c
  ax₆ _ _ _ b (inr c)         | no b≠c | no _  = sym $ ifᵈ-≠ b≠c ∙ refl
  ax₆ _ _ _ _ (inr _)         | no _ | yes _ = refl
  ax₆ _ j a b (inr c) ⦃ a≠b ⦄ | yes b≡c =
    sym $ ap (cls j b) (ifᵈ-≠ a≠c) ∙ ifᵈ-≡ b≡c
    where a≠c = λ H≡ → is-no-false a≠b (H≡ ∙ sym b≡c)

  ax₇ :
    (i j : Nat)
    (a b : 𝔸)
    (x : Nat𝔸)
    ⦃ p : i ≠ j ⦄
    ⦃ q : a ≠ b ⦄
    → ---------------------------------------
    opn i a (cls j b x) ≡ cls j b (opn i a x)
  ax₇ i _ _ _ (inl k)             with i ≡? k
  ax₇ _ _ _ _ (inl _)             | no _  = refl
  ax₇ _ _ a b (inl _) ⦃ q = b≡a ⦄ | yes _ = sym $ ifᵈ-≠ (is-no-false b≡a ∘ sym)
  ax₇ _ _ _ b (inr c)             with b ≡? c
  ax₇ _ _ _ _ (inr _)             | no _  = refl
  ax₇ i j _ _ (inr _) ⦃ i≠j ⦄     | yes _ = ifᵈ-≠ (is-no-false i≠j)

  ax₈ :
    (i j : Nat)
    (a b : 𝔸)
    (x : Nat𝔸)
    → -----------------------------------------------------------
    opn i b (cls i a (opn j b x)) ≡ opn j b (cls j a (opn i a x))
  ax₈ _ j _ _ (inl k) with j ≡? k
  ax₈ i _ _ _ (inl k) | no _ with i ≡? k
  ax₈ _ j _ _ (inl k) | no j≠k | no _  = sym $ ifᵈ-≠ j≠k
  ax₈ _ j a b (inl _) | no _   | yes _ = sym $
    ap (opn j b) (ifᵈ-≡ (refl' a)) ∙ ifᵈ-≡ (refl' j)
  ax₈ _ _ a b (inl _) | yes j≡k with a ≡? b
  ax₈ i j _ _ (inl _) | yes j≡k | no _ with i ≡? j
  ax₈ i j a b (inl k) | yes j≡k | no _ | no i≠j = sym $
    ap (opn j b ∘ cls j a) (ifᵈ-≠ i≠k) ∙ ifᵈ-≡ j≡k
    where i≠k = λ H≡ → i≠j (H≡ ∙ sym j≡k)
  ax₈ i j a b (inl k) | yes j≡k | no _ | yes i≡j = sym $
    ap (opn j b ∘ cls j a) (ifᵈ-≡ (i≡j ∙ j≡k)) ∙
    ap (opn j b) (ifᵈ-≡ (refl' a)) ∙ ifᵈ-≡ (refl' j)
  ax₈ i j _ _ (inl _) | yes j≡k | yes _ with i ≡? j
  ax₈ i j a b (inl k) | yes j≡k | yes _ | no i≠j = sym $
    ap (opn j b ∘ cls j a) (ifᵈ-≠ i≠k) ∙ ifᵈ-≡ j≡k ∙
    sym (ifᵈ-≡ (refl {x = i}))
    where i≠k = λ H≡ → i≠j (H≡ ∙ sym j≡k)
  ax₈ i j a b (inl k) | yes j≡k | yes _ | yes i≡j = sym $
    ap (opn j b ∘ cls j a) (ifᵈ-≡ (i≡j ∙ j≡k)) ∙
    ap (opn j b) (ifᵈ-≡ (refl' a)) ∙ ifᵈ-≡ (refl' j) ∙
    sym (ifᵈ-≡ (refl' i))
  ax₈ _ _ a _ (inr c) with a ≡? c
  ax₈ _ _ _ _ (inr _) | no _ = refl
  ax₈ i j _ _ (inr _) | yes _ = ifᵈ-≡ (refl' i) ∙ sym (ifᵈ-≡ (refl' j))

  ax₉ :
    (i j : Nat)
    (a b : 𝔸)
    (x : Nat𝔸)
    → -----------------------------------------------------------
    cls j a (opn i a (cls j b x)) ≡ cls j b (opn i b (cls i a x))
  ax₉ i _ _ _ (inl k) with i ≡? k
  ax₉ _ _ _ _ (inl _) | no _ = refl
  ax₉ _ _ a b (inl _) | yes p = ifᵈ-≡ (refl' a) ∙ sym (ifᵈ-≡ (refl' b))
  ax₉ _ _ _ b (inr c) with b ≡? c
  ax₉ _ _ a _ (inr c) | no _ with a ≡? c
  ax₉ _ _ _ b (inr _) | no b≠c | no _ = sym $ ifᵈ-≠ b≠c
  ax₉ i j _ b (inr _) | no _ | yes _ = sym $
    ap (cls j b) (ifᵈ-≡ (refl' i)) ∙ ifᵈ-≡ (refl' b) 
  ax₉ i j a b (inr _) | yes b≡c with i ≡? j
  ax₉ _ _ a b (inr _) | yes b≡c | no _ with a ≡? b
  ax₉ i j a b (inr _) | yes b≡c | no _ | no a≠b = sym $
    ap (cls j b ∘ opn i b) (ifᵈ-≠ a≠c) ∙ ifᵈ-≡ b≡c
    where a≠c = λ H≡ → a≠b (H≡ ∙ sym b≡c)
  ax₉ i j a b (inr _) | yes b≡c | no _ | yes a≡b = sym $
    ap (cls j b ∘ opn i b) (ifᵈ-≡ (a≡b ∙ b≡c)) ∙
    ap (cls j b) (ifᵈ-≡ (refl' i)) ∙ ifᵈ-≡ (refl' b)
  ax₉ _ _ a b (inr _) | yes b≡c | yes _ with a ≡? b
  ax₉ i j a b (inr _) | yes b≡c | yes _ | no a≠b = sym $
    ap (cls j b ∘ opn i b) (ifᵈ-≠ a≠c) ∙ ifᵈ-≡ b≡c ∙
    sym (ifᵈ-≡ (refl' a))
    where a≠c = λ H≡ → a≠b (H≡ ∙ sym b≡c)
  ax₉ i j a b (inr _) | yes b≡c | yes _ | yes a≡b = sym $
    ap (cls j b ∘ opn i b) (ifᵈ-≡ (a≡b ∙ b≡c)) ∙
    ap (cls j b) (ifᵈ-≡ (refl' i)) ∙ ifᵈ-≡ (refl' b) ∙
    sym (ifᵈ-≡ (refl' a))

instance
  ocNat𝔸 : oc Nat𝔸
  ocNat𝔸 = mkoc opn cls ax₁ ax₂ ax₃ ax₄ ax₅ ax₆ ax₇ ax₈ ax₉

-- Nat𝔸 is unfinite
instance
  Unfinite-Nat𝔸 : Unfinite Nat𝔸
  Unfinite-Nat𝔸 = Unfinite-⊎

----------------------------------------------------------------------
-- Product of oc-sets
----------------------------------------------------------------------
oc× :
  {X Y : Type}
  ⦃ _ : oc X ⦄
  ⦃ _ : oc Y ⦄
  → ----------
  oc (X × Y)
_~>_ ⦃ oc× ⦄ i a (x , y) = (i ~> a)x , (i ~> a)y
_<~_ ⦃ oc× ⦄ i a (x , y) = (i <~ a)x , (i <~ a)y
oc₁ ⦃ oc× ⦄ i a b (x , y) = ap₂ _,_ (oc₁ i a b x) (oc₁ i a b y)
oc₂ ⦃ oc× ⦄ i j a (x , y) = ap₂ _,_ (oc₂ i j a x) (oc₂ i j a y)
oc₃ ⦃ oc× ⦄ i a (x , y) = ap₂ _,_ (oc₃ i a x) (oc₃ i a y)
oc₄ ⦃ oc× ⦄ i a (x , y) = ap₂ _,_ (oc₄ i a x) (oc₄ i a y)
oc₅ ⦃ oc× ⦄ i j a b (x , y) = ap₂ _,_ (oc₅ i j a b x) (oc₅ i j a b y)
oc₆ ⦃ oc× ⦄ i j a b (x , y) = ap₂ _,_ (oc₆ i j a b x) (oc₆ i j a b y)
oc₇ ⦃ oc× ⦄ i j a b (x , y) = ap₂ _,_ (oc₇ i j a b x) (oc₇ i j a b y)
oc₈ ⦃ oc× ⦄ i j a b (x , y) = ap₂ _,_ (oc₈ i j a b x) (oc₈ i j a b y)
oc₉ ⦃ oc× ⦄ i j a b (x , y) = ap₂ _,_ (oc₉ i j a b x) (oc₉ i j a b y)
