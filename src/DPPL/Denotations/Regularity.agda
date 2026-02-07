open import Lib.Algebra.Reals

module DPPL.Denotations.Regularity (R : Reals₀) where

open import DPPL.Regularity
open import Lib.Prelude
open import Lib.Data.Dec
open import Lib.Data.Vector

open import Data.Dec.Base
open import Data.Power

open Reals R using (ℝ)
open Reg↓≤ using (_≤_ ; ≤-trans)

private variable
  m n : Nat
  c c' : Reg↓

is-const : ℙ (ℝ ^ m → ℝ ^ n)
is-const {n = n} f = elΩ (Σ[ x ∈ ℝ ^ n ] f ≡ λ _ → x)

record RegAssumptions : Type₁ where
  field
    ⟨_⟩-reg : Reg↓ → ∀ {m n} → ℙ (ℝ ^ m → ℝ ^ n)
    ⊆-reg : c ≤ c' → ⟨ c' ⟩-reg {m} {n} ⊆ ⟨ c ⟩-reg

    id-reg : (λ x → x) ∈ ⟨ c ⟩-reg {m}
    const-reg : (x : ℝ ^ n) → (λ _ → x) ∈ ⟨ c ⟩-reg {m}
    ∘-reg
      : {m n k : Nat} {f : ℝ ^ n → ℝ ^ k} {g : ℝ ^ m → ℝ ^ n}
      → f ∈ ⟨ c ⟩-reg → g ∈ ⟨ c ⟩-reg → f ∘ g ∈ ⟨ c ⟩-reg

  ⟨_∣_⟩-reg : Reg↓ → Reg↓ → ∀ {m n} → ℙ (ℝ ^ m → ℝ ^ n)
  ⟨_∣_⟩-reg c d =
    ifᵈ holds? (c ≤ d) then
      ⟨ c ⟩-reg
    else
      is-const

module RegProperties (Ax : RegAssumptions) where
  open RegAssumptions Ax

  ⟨∣⟩-reg-≤ : c ≤ c' → ⟨ c ∣ c' ⟩-reg {m} {n} ≡ ⟨ c ⟩-reg
  ⟨∣⟩-reg-≤ {c = c} {c'} H≤ = ifᵈ-yes (holds? (c ≤ c')) (true→is-yes H≤)

  ⟨∣⟩-reg-≰ : ¬ c ≤ c' → ⟨ c ∣ c' ⟩-reg {m} {n} ≡ is-const
  ⟨∣⟩-reg-≰ {c = c} {c'} H≰ = ifᵈ-no (holds? (c ≤ c')) (false→is-no H≰)

  id-reg' : c ≤ c' → (λ x → x) ∈ ⟨ c ∣ c' ⟩-reg {m}
  id-reg' H≤ = subst ((λ x → x) ∈_) (sym $ ⟨∣⟩-reg-≤ H≤) id-reg

  const-reg' : (x : ℝ ^ n) → (λ _ → x) ∈ ⟨ c ∣ c' ⟩-reg {m}
  const-reg' {c = c} {c'} x with holds? (c ≤ c')
  ... | yes _ = const-reg x
  ... | no  _ = inc (_ , refl)

  ∘-reg'
    : {c d e : Reg↓} {m n k : Nat} {f : ℝ ^ n → ℝ ^ k} {g : ℝ ^ m → ℝ ^ n}
    → f ∈ ⟨ d ∣ e ⟩-reg → g ∈ ⟨ c ∣ d ⟩-reg → f ∘ g ∈ ⟨ c ∣ e ⟩-reg
  ∘-reg' {c} {d} {e} {f = f} {g} Hf Hg with holds? (c ≤ d) | holds? (d ≤ e)
  ... | no c≰d | _ =
    □-rec (⟨ c ∣ e ⟩-reg _ .is-tr)
      (λ (x , Hg') → subst (λ g → f ∘ g ∈ ⟨ c ∣ e ⟩-reg) (sym Hg') (const-reg' (f x)))
      Hg
  ... | yes c≤d | no d≰e =
    □-rec (⟨ c ∣ e ⟩-reg _ .is-tr)
      (λ (x , Hf') → subst (λ f → f ∘ g ∈ ⟨ c ∣ e ⟩-reg) (sym Hf') (const-reg' x))
      Hf
  ... | yes c≤d | yes d≤e =
    subst (_ ∈_) (sym $ ⟨∣⟩-reg-≤ (≤-trans c≤d d≤e)) (∘-reg (⊆-reg c≤d _ Hf) Hg)
