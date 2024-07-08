module Properties.Util where

-- Lemmas regarding substitution and other utility lemmas

open import Lib.Prelude
open import Lib.Unfinite
open import Lib.LocalClosedness
open import Lib.oc-Sets
open import Lib.FunExt
open import Lib.BindingSignature

open import Function using (_$_)
open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.Product using (∃-syntax)

module _ {Σ : Sig} where
  open Subst {Σ}

  subst-open-comm
    : ∀ {x y n u} t
    → y ≠ x
    → 0 ≻ u
    → -----------------------------------------
      (x => u)((n ~> y)t) ≡ (n ~> y)((x => u)t)
  subst-open-comm {x} {y} {n} (bvar x₁) Hneq Hlc with n ≐ x₁
  ... | neq _ = refl
  ... | equ with x ≐ y
  ...   | neq _ = refl
  ...   | equ rewrite dec-equ x with () ← Hneq
  subst-open-comm {x} {y} {n} (fvar y₁) Hneq Hlc with x ≐ y₁
  ... | neq _ = refl
  ... | equ rewrite ≻3 {j = n} {y} Hlc 0≤ = refl
  subst-open-comm (op (o , ts)) Hneq Hlc =
    ap (op ∘ (o ,_)) $ funext λ i → subst-open-comm (ts i) Hneq Hlc


all-⊎
  : ∀ {n} {A B : Fin n → Set}
  → (∀ i → A i ⊎ B i)
  → -------------------------------------------------------
    (∀ i → A i) ⊎ ∃[ j ] B j × ∀ (i : Fin n) → i <ꟳ j → A i

all-⊎ {zero} f = ι₁ λ()
all-⊎ {n +1} f =
  case (f zero) λ
    { (ι₁ Ha) →
      case (all-⊎ (f ∘ succ)) λ
        { (ι₁ Has) → ι₁ $ λ { zero → Ha ; (succ n) → Has n }
        ; (ι₂ (j , Hb , Has)) → ι₂ $
          _ , Hb , λ { zero _ → Ha ; (succ n) H≤ → Has n (≤-1 H≤) }
        }
    ; (ι₂ Hb) → ι₂ $ _ , Hb , λ _ ()
    }

