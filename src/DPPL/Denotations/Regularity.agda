open import Data.Power

open import DPPL.Regularity

open import Homotopy.Join

open import Lib.Algebra.Reals
open import Lib.Data.Vector
open import Lib.Prelude

module DPPL.Denotations.Regularity (R : Reals₀) where

open Reals R using (ℝ)
open Reg≤ using (_≤_ ; ≤-trans)

private variable
  m n : Nat
  c c' : Reg

is-const : ℙ (ℝ ^ m → ℝ ^ n)
is-const {n = n} f = elΩ $ Σ[ x ∈ ℝ ^ n ] f ≡ λ _ → x

record RegAssumptions : Type₁ where
  field
    ⟨_⟩-reg : Reg → ∀ {m n} → ℙ (ℝ ^ m → ℝ ^ n)
    ⊆-reg : c ≤ c' → ⟨ c' ⟩-reg {m} {n} ⊆ ⟨ c ⟩-reg

    id-reg : (λ x → x) ∈ ⟨ c ⟩-reg {m}
    const-reg : (x : ℝ ^ n) → (λ _ → x) ∈ ⟨ c ⟩-reg {m}
    ∘-reg
      : {m n k : Nat} {f : ℝ ^ n → ℝ ^ k} {g : ℝ ^ m → ℝ ^ n}
      → f ∈ ⟨ c ⟩-reg → g ∈ ⟨ c ⟩-reg → f ∘ g ∈ ⟨ c ⟩-reg

  ⟨_∣_⟩-reg : Reg → Reg → ∀ {m n} → ℙ (ℝ ^ m → ℝ ^ n)
  ⟨ c ∣ d ⟩-reg f .∣_∣   = (c ≤ d × f ∈ ⟨ c ⟩-reg) ∗ (f ∈ is-const)
  ⟨ c ∣ d ⟩-reg f .is-tr = join-is-prop (hlevel 1) (hlevel 1)

module RegProperties (Ax : RegAssumptions) where
  open RegAssumptions Ax

  id-reg' : c ≤ c' → (λ x → x) ∈ ⟨ c ∣ c' ⟩-reg {m}
  id-reg' H≤ = inl (H≤ , id-reg)

  const-reg' : (x : ℝ ^ n) → (λ _ → x) ∈ ⟨ c ∣ c' ⟩-reg {m}
  const-reg' x = inr (inc (x , refl))

  ∘-reg'
    : {c d e : Reg} {m n k : Nat} {f : ℝ ^ n → ℝ ^ k} {g : ℝ ^ m → ℝ ^ n}
    → f ∈ ⟨ d ∣ e ⟩-reg → g ∈ ⟨ c ∣ d ⟩-reg → f ∘ g ∈ ⟨ c ∣ e ⟩-reg
  ∘-reg' {f = f} {g} Hf Hg =
    case Hf of join-elim-prop (λ _ → ⟨ _ ∣ _ ⟩-reg _ .is-tr)
      (λ (H≤ , Hf') → case Hg of join-elim-prop (λ _ → ⟨ _ ∣ _ ⟩-reg _ .is-tr)
        (λ (H≤' , Hg') → inl (≤-trans H≤' H≤ , ∘-reg (⊆-reg H≤' _ Hf') Hg'))
        λ Hconst → inr (case Hconst of λ x p → inc (f x , ap (f ∘_) p)))
      λ Hconst → inr (case Hconst of λ x p → inc (x , ap (_∘ g) p))
