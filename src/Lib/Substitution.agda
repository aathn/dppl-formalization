module Lib.Substitution where

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.oc-Sets
open import Lib.LocalClosedness
open import Lib.FunExt
open import Lib.BindingSignature

module _ {Σ : Sig} where

  Subst : Set
  Subst = (ℕ𝔸 → Trm Σ) → Trm Σ
  
  var-subst : ℕ𝔸 → Subst
  var-subst na ρ = ρ na
  
  alg-subst : Σ ∙ Subst → Subst
  alg-subst (o , f) ρ = op (o , λ k → f k ρ)
  
  substTrm : Trm Σ → Subst
  substTrm = UniversalProperty.rec var-subst alg-subst
  
  -- Free variable substitution
  _=>_ : 𝔸 → Trm Σ → Trm Σ → Trm Σ
  (a => u) t = substTrm t ρ
    where
    ρ : ℕ𝔸 → Trm Σ
    ρ (ι₁ x) = bvar x
    ρ (ι₂ y) = if does(a ≐ y) then u else fvar y
  
  -- Bound variable substitution
  _≈>_ : ℕ → Trm Σ → Trm Σ → Trm Σ
  (n ≈> u) (bvar x) = if does(n ≐ x) then u else bvar x
  (n ≈> u) (fvar y) = fvar y
  (n ≈> u) (op (o , ts)) = op (o , λ k → ((n + index (ar Σ o) k) ≈> u) (ts k))

  subst-open-comm
    : ∀ {x y n u} t
    → x ≠ y
    → 0 ≻ u
    → -----------------------------------------
      (x => u)((n ~> y)t) ≡ (n ~> y)((x => u)t)
  subst-open-comm {x} {y} {n} (bvar x₁) Hneq Hlc with n ≐ x₁
  ... | neq _ = refl
  ... | equ rewrite Hneq = refl
  subst-open-comm {x} {y} {n} (fvar y₁) Hneq Hlc with x ≐ y₁
  ... | neq _ = refl
  ... | equ rewrite ≻3 {j = n} {y} Hlc 0≤ = refl
  subst-open-comm (op (o , ts)) Hneq Hlc =
    ap (op ∘ (o ,_)) $ funext λ i → subst-open-comm (ts i) Hneq Hlc

  subst-intro
    : ∀ {x n u} t
    → x ∉ fv t
    → -------------------------------
      (n ≈> u)t ≡ (x => u)((n ~> x)t)
  subst-intro {x} {n} (bvar x₁) H∉ with n ≐ x₁
  ... | neq _ = refl
  ... | equ rewrite dec-equ x = refl
  subst-intro {x} (fvar y) H∉ with x ≐ y | H∉
  ... | neq _ | _   = refl
  ... | equ   | ∉[] with () ← ¬≠ x it
  subst-intro {x} {n} {u} (op (o , ts)) H∉ =
    ap (op ∘ (o ,_)) $ funext λ i → subst-intro (ts i) (∉⋃ _ i {{H∉}})

  subst-fresh
    : ∀ {x} u t
    → x ∉ fv t
    → --------------
      (x => u) t ≡ t
  subst-fresh u (bvar x) H∉ = refl
  subst-fresh u (fvar y) (∉[] {{p}}) rewrite p = refl
  subst-fresh u (op (o , ts)) H∉ =
    ap (op ∘ (o ,_)) $ funext λ i → subst-fresh u (ts i) (∉⋃ _ i {{H∉}})

  open-notin
    : ∀ {x y n} t
    → x ∉ fv {Σ} ((n ~> y) t)
    → x ∉ fv t
  open-notin (bvar x) H∉ = ∉Ø
  open-notin (fvar y) H∉ = H∉
  open-notin (op (o , ts)) H∉ =
    ∉⋃′ (fv ∘ ts) λ i → open-notin (ts i) (∉⋃ _ i {{H∉}})
