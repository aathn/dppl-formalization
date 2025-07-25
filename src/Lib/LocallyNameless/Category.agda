--------------------------------------------------------------
-- This file was adapted from the code accompanying the paper
--
-- Andrew M. Pitts, "Locally Nameless Sets", POPL 2023
--
-- (© 2023 Andrew Pitts, University of Cambridge)
--
-- https://amp12.github.io/LocallyNamelessSets/
--------------------------------------------------------------

module Lib.LocallyNameless.Category where

open import Lib.Prelude
open import Lib.Finset
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets
open import Lib.LocallyNameless.Freshness
open import Lib.LocallyNameless.LocalClosedness
open import Lib.LocallyNameless.Support
open import Lib.LocallyNameless.AbstractionConcretion
open import Lib.LocallyNameless.RenamingReindexingSwapping

open FinsetSyntax
open NatOrd

----------------------------------------------------------------------
-- Morphisms of oc-sets [Equation (40)]
----------------------------------------------------------------------
record oc-hom
  {X Y : Type}
  ⦃ _ : oc X ⦄
  ⦃ _ : oc Y ⦄
  (f : X → Y)
  : ----------
  Type
  where
  constructor mkoc-hom
  field
    oc-hom-open  : ∀{i a} x → f((i ~> a)x) ≡ (i ~> a)(f x)
    oc-hom-close : ∀{i a} x → f((i <~ a)x) ≡ (i <~ a)(f x)

open oc-hom ⦃ ... ⦄ public

module _
  (X Y : Type)
  ⦃ _ : oc X ⦄
  ⦃ _ : oc Y ⦄
  (f : X → Y)
  ⦃ _ :  oc-hom f ⦄
  where
  oc-hom-# : ∀ a x → a # x → a # f x -- Equation (41)
  oc-hom-# a x a#x =
    (0 <~ a)(f x) ≡˘⟨ oc-hom-close x ⟩
    f((0 <~ a)x)  ≡⟨ ap f a#x ⟩
    f x           ∎

  oc-hom-≻ : ∀ i x → i ≻ x → i ≻ f x -- Equation (42)
  oc-hom-≻  i x i≻x j with (a , e) ← i≻x j = (a ,
    ((j ~> a) (f x) ≡˘⟨ oc-hom-open x ⟩
     f((j ~> a)x)   ≡⟨ ap f e ⟩
     f x            ∎))

----------------------------------------------------------------------
-- Morphisms of locally nameless sets [Section 3.2]
----------------------------------------------------------------------
record lns-hom
  {X Y : Type}
  ⦃ _ : lns X ⦄
  ⦃ _ : lns Y ⦄
  (f : X → Y)
  : -----------
  Type
  where
  constructor mklns-hom
  field
    ⦃ ochom ⦄ : oc-hom f

open lns-hom ⦃ ... ⦄ public

----------------------------------------------------------------------
-- Cartesian product of locally nameless sets [Lemma 3.3]
----------------------------------------------------------------------
lns× : {X Y : Type}⦃ _ : lns X ⦄ ⦃ _ : lns Y ⦄ → lns (X × Y)
ocSet ⦃ lns× ⦄ = oc×
asupp ⦃ lns× ⦄ (x , y) with Иi as f ← asupp x | Иi bs g ← asupp y =
  Иi (as ∪ bs) h
  where
  h :
    (c : 𝔸)
    ⦃ _ : c ∉ (as ∪ bs) ⦄
    → -------------------------------
    ((0 <~ c)x , (0 <~ c)y) ≡ (x , y)
  h c ⦃ p ⦄ = ap₂ _,_ (f c ⦃ ∉∪₁ p ⦄) (g c ⦃ ∉∪₂ as p ⦄)
isupp ⦃ lns× ⦄ (x , y) with (i , p) ← isupp x | (j , q) ← isupp y =
  (max i j , h)
  where
  h :
    (k : Nat)
    ⦃ _ : max i j ≤ k ⦄
    → -----------------------------------------
    Σ[ c ∈ 𝔸 ] ((k ~> c)x , (k ~> c)y) ≡ (x , y)
  h k ⦃ r ⦄
    with (a , e) ← p k ⦃ ≤-trans (max-≤l _ _) r ⦄
    | (b , e') ← q k ⦃ ≤-trans (max-≤r _ _) r ⦄ = (a , ee')
    where
    ee' : ((k ~> a)x , (k ~> a)y) ≡ (x , y)
    ee' = ap₂ _,_ e (≻2 e')

----------------------------------------------------------------------
-- Dependent product of locally nameless sets
----------------------------------------------------------------------
ocΣ :
  (X : Type)
  (Y : X → Type)
  ⦃ ocY : ∀{x} → oc (Y x) ⦄
  → -----------------------
  oc (Σ X Y)
_~>_ ⦃ ocΣ X Y ⦄ i a (x , y) = (x , (i ~> a)y)
_<~_ ⦃ ocΣ X Y ⦄ i a (x , y) = (x , (i <~ a)y)
oc₁  ⦃ ocΣ X Y ⦄ i a b (_ , y) = ap (_ ,_) (oc₁ i a b y)
oc₂  ⦃ ocΣ X Y ⦄ i j a (_ , y) = ap (_ ,_) (oc₂ i j a y)
oc₃  ⦃ ocΣ X Y ⦄ i a (_ , y) = ap (_ ,_) (oc₃ i a y)
oc₄  ⦃ ocΣ X Y ⦄ i a (_ , y) = ap (_ ,_) (oc₄ i a y)
oc₅  ⦃ ocΣ X Y ⦄ i j a b (_ , y) = ap (_ ,_) (oc₅ i j a b y)
oc₆  ⦃ ocΣ X Y ⦄ i j a b (_ , y) = ap (_ ,_) (oc₆ i j a b y)
oc₇  ⦃ ocΣ X Y ⦄ i j a b (_ , y) = ap (_ ,_) (oc₇ i j a b y)
oc₈  ⦃ ocΣ X Y ⦄  i j a b (_ , y) = ap (_ ,_) (oc₈ i j a b y)
oc₉  ⦃ ocΣ X Y ⦄ i j a b (_ , y) = ap (_ ,_) (oc₉ i j a b y)

lnsΣ :
  (X : Type)
  (Y : X → Type)
  ⦃ lnsY : ∀{x} → lns (Y x) ⦄
  → -------------------------
  lns (Σ X Y)
ocSet ⦃ lnsΣ X Y ⦃ lnsY ⦄ ⦄ = ocΣ X Y ⦃ λ{x} → ocSet ⦃ lnsY {x} ⦄ ⦄
asupp ⦃ lnsΣ X Y ⦃ lnsY ⦄ ⦄ (x , y) with Иi и₁ и₂ ← asupp y = Иi и₁ и₂'
  where
  instance
    _ : oc (Y x)
    _ = ocSet ⦃ lnsY {x} ⦄
  и₂' :
    (a : 𝔸)
    ⦃ _ : a ∉ и₁ ⦄
    → ------------------------
    (x , (0 <~ a) y) ≡ (x , y)
  и₂' a = ap (x ,_) (и₂ a)
isupp ⦃ lnsΣ X Y ⦃ lnsY ⦄ ⦄ (x , y) with (i , f) ← isupp y = (i , g)
  where
  instance
    _ : oc (Y x)
    _ = ocSet ⦃ lnsY {x} ⦄
  g :
    (j : Nat)
    ⦃ _ : i ≤ j ⦄
    → ----------------------------------
    Σ[ a ∈ 𝔸 ] (x , (j ~> a) y) ≡ (x , y)
  g j with (a , p) ← f j = (a , ap (x ,_) p)
