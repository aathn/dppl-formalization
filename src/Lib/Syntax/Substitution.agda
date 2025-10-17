module Lib.Syntax.Substitution where

open import Lib.Prelude
open import Lib.Data.Dec
open import Lib.Data.Finset
open import Lib.Data.Vector
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.oc-Sets
open import Lib.LocallyNameless.LocalClosedness
open import Lib.LocallyNameless.BindingSignature

module _ {Σ : Sig} where

  Subst : Type
  Subst = (Nat𝔸 → Trm Σ) → Trm Σ
  
  var-subst : Nat𝔸 → Subst
  var-subst na ρ = ρ na
  
  alg-subst : Σ ◆ Subst → Subst
  alg-subst (o , f) ρ = op (o , λ k → f k ρ)
  
  subst-trm : Trm Σ → Subst
  subst-trm = UniversalProperty.rec var-subst alg-subst
  
  -- Free variable substitution
  _=>_ : 𝔸 → Trm Σ → Trm Σ → Trm Σ
  (a => u) t = subst-trm t ρ
    where
    ρ : Nat𝔸 → Trm Σ
    ρ (inl x) = bvar x
    ρ (inr y) = ifᵈ a ≡? y then u else fvar y
  
  -- Bound variable substitution
  _≈>_ : Nat → Trm Σ → Trm Σ → Trm Σ
  (n ≈> u) (bvar x) = ifᵈ n ≡? x then u else bvar x
  (n ≈> u) (fvar y) = fvar y
  (n ≈> u) (op (o , ts)) = op (o , λ k → ((n + index (ar Σ o) k) ≈> u) (ts k))

  subst-open-comm
    : ∀ {x y n u} t
    → x ≠ y
    → 0 ≻ u
    → -----------------------------------------
      (x => u)((n ~> y)t) ≡ (n ~> y)((x => u)t)
  subst-open-comm {x} {y} {n} (bvar x₁) Hneq Hlc with n ≡? x₁
  ... | no _  = refl
  ... | yes p = ifᵈ-no _ Hneq
  subst-open-comm {x} {y} {n} (fvar y₁) Hneq Hlc with x ≡? y₁
  ... | no _  = refl
  ... | yes p = sym $ ≻3 {j = n} {y} Hlc 0≤x
  subst-open-comm (op (o , ts)) Hneq Hlc =
    ap (op ∘ (o ,_)) $ funext λ i → subst-open-comm (ts i) Hneq Hlc

  subst-intro
    : ∀ {x n u} t
    → x ∉ fv t
    → -------------------------------
      (n ≈> u)t ≡ (x => u)((n ~> x)t)
  subst-intro {x} {n} (bvar x₁) H∉ with n ≡? x₁
  ... | no _  = refl
  ... | yes p = sym $ ifᵈ-≡ {a = x} refl
  subst-intro {x} (fvar y) H∉ with x ≡? y
  ... | no _ = refl
  ... | yes p with () ← H∉
  subst-intro {x} {n} {u} (op (o , ts)) H∉ =
    ap (op ∘ (o ,_)) $ funext λ i → subst-intro (ts i) (∉⋃ _ i {{H∉}})

  subst-fresh
    : ∀ {x} u t
    → x ∉ fv t
    → --------------
      (x => u) t ≡ t
  subst-fresh u (bvar x) H∉ = refl
  subst-fresh u (fvar y) H∉ = ifᵈ-no _ (∉∷₁ H∉)
  subst-fresh u (op (o , ts)) H∉ =
    ap (op ∘ (o ,_)) $ funext λ i → subst-fresh u (ts i) (∉⋃ _ i {{H∉}})

  open-notin
    : ∀ {x y : 𝔸} {n} t
    → x ∉ fv {Σ} ((n ~> y) t)
    → x ∉ fv t
  open-notin (bvar x) H∉ = tt
  open-notin (fvar y) H∉ = H∉
  open-notin (op (o , ts)) H∉ =
    ∉⋃' (fv ∘ ts) λ i → open-notin (ts i) (∉⋃ _ i {{H∉}})
