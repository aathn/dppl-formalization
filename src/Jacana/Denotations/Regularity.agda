open import 1Lab.Prelude

open import Data.Nat.Base using (H-Level-≤)
open import Data.Power

open import Jacana.Regularity

open import Lib.Homotopy.Join

open import Lib.Algebra.Reals
open import Lib.Data.Vector

module Jacana.Denotations.Regularity where

is-const : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → ℙ (A → B)
is-const {B = B} f = elΩ $ Σ[ x ∈ B ] f ≡ λ _ → x

module _ (R : Reals₀) where
  open Reals R using (ℝ)
  open Reg≤

  private variable
    c c' : Reg

  private module open-set (⟨_⟩-open : Reg → ∀ {m} → ℙ (ℙ (ℝ ^ m))) where
    record ⟨_⟩-open-set (c : Reg) : Type where
      constructor mk-open-set
      field
        {dim}   : Nat
        {set}   : ℙ (ℝ ^ dim)
        is-open : ∣ ⟨ c ⟩-open set ∣
    open ⟨_⟩-open-set public

  record RegAssumptions : Type₁ where

    _×ₛ_ : ∀ {m n} → ℙ (ℝ ^ m) → ℙ (ℝ ^ n) → ℙ (ℝ ^ (m + n))
    _×ₛ_ {m} U V xy =
      let x , y = split {m = m} xy in
      el (x ∈ U × y ∈ V) (hlevel 1)

    field
      ⟨_⟩-open : Reg → ∀ {m} → ℙ (ℙ (ℝ ^ m))
      ⊆-open   : c ≤ c' → ∀ {m} → ⟨ c' ⟩-open {m} ⊆ ⟨ c ⟩-open
      ×-open
        : ∀ {m n} {U : ℙ (ℝ ^ m)} {V : ℙ (ℝ ^ n)}
        → U ∈ ⟨ c ⟩-open → V ∈ ⟨ c ⟩-open
        → (U ×ₛ V) ∈ ⟨ c ⟩-open
      ⊤-open : ∀ m → maximal ∈ ⟨ c ⟩-open {m}

    open open-set ⟨_⟩-open public

    ⊆-open-set : c ≤ c' → ⟨ c' ⟩-open-set → ⟨ c ⟩-open-set
    ⊆-open-set H≤ U = mk-open-set (⊆-open H≤ _ (U .is-open))

    ℝ-open-set : ∀ m → ⟨ c ⟩-open-set
    ℝ-open-set m = mk-open-set (⊤-open m)

    ×-open-set : ⟨ c ⟩-open-set → ⟨ c ⟩-open-set → ⟨ c ⟩-open-set
    ×-open-set U V = mk-open-set (×-open (U .is-open) (V .is-open))

    ∣_∣ₛ : ⟨ c ⟩-open-set → Type
    ∣ U ∣ₛ = ∫ₚ (U .set)

    to-×ₛ : (U V : ⟨ c ⟩-open-set) → ∣ U ∣ₛ × ∣ V ∣ₛ → ∣ ×-open-set U V ∣ₛ
    to-×ₛ U V (x , y) =
      x .fst ++ y .fst
      , subst (_∈ U .set) (sym $ ap fst (Equiv.ε (vec-sum-prod (U .dim)) _)) (x .snd)
      , subst (_∈ V .set) (sym $ ap snd (Equiv.ε (vec-sum-prod (U .dim)) _)) (y .snd)

    from-×ₛ : (U V : ⟨ c ⟩-open-set) → ∣ ×-open-set U V ∣ₛ → ∣ U ∣ₛ × ∣ V ∣ₛ
    from-×ₛ U V (xy , p , q) = let x , y = split {m = U .dim} xy in (x , p) , (y , q)

    pbₛ
      : (U V : ⟨ c ⟩-open-set) (f : ∣ U ∣ₛ → ∣ V ∣ₛ)
      → ℙ (ℝ ^ V .dim) → ℙ (ℝ ^ U .dim)
    pbₛ U V f W x = elΩ $ Σ[ Hx ∈ x ∈ U .set ] f (x , Hx) .fst ∈ W

    pb-⊆ : ∀ (U V : ⟨ c ⟩-open-set) f W → pbₛ U V f W ⊆ U .set
    pb-⊆ U V f W _ Hx = case Hx of λ H∈ _ → H∈

    pb-projₛ
      : (U V : ⟨ c ⟩-open-set) (f : ∣ U ∣ₛ → ∣ V ∣ₛ) (W : ℙ (ℝ ^ V .dim))
      → ∫ₚ (pbₛ U V f W) → ∫ₚ W
    pb-projₛ U V f W (x , Hx) =
        f (x , pb-⊆ U V f W _ Hx) .fst
      , case Hx of λ _ p → subst (λ x → ∣ W (f x .fst) ∣) (Σ-prop-path! refl) p

    field
      ⟨_⟩-reg : (c : Reg) (U V : ⟨ c ⟩-open-set) → ℙ (∣ U ∣ₛ → ∣ V ∣ₛ)
      ⊆-reg
        : ∀ {U V} (H≤ : c ≤ c')
        → ⟨ c' ⟩-reg U V ⊆ ⟨ c ⟩-reg (⊆-open-set H≤ U) (⊆-open-set H≤ V)

      id-reg     : ∀ {U} → (λ x → x) ∈ ⟨ c ⟩-reg U U
      ∘-reg
        : ∀ {U V W f g}
        → f ∈ ⟨ c ⟩-reg V W → g ∈ ⟨ c ⟩-reg U V → f ∘ g ∈ ⟨ c ⟩-reg U W

      tup-reg
        : ∀ {U V W f g}
        → f ∈ ⟨ c ⟩-reg U V → g ∈ ⟨ c ⟩-reg U W
        → to-×ₛ V W ∘ ⟨ f , g ⟩ ∈ ⟨ c ⟩-reg U (×-open-set V W)
      proj-reg₁ : ∀ {U V} → fst ∘ from-×ₛ U V ∈ ⟨ c ⟩-reg (×-open-set U V) U
      proj-reg₂ : ∀ {U V} → snd ∘ from-×ₛ U V ∈ ⟨ c ⟩-reg (×-open-set U V) V

      pb-open
        : ∀ {U V W f} → f ∈ ⟨ c ⟩-reg U V → W ∈ ⟨ c ⟩-open
        → pbₛ U V f W ∈ ⟨ c ⟩-open
      pb-proj-reg
        : ∀ {U V W f} (Hf : f ∈ ⟨ c ⟩-reg U V) (HW : W ∈ ⟨ c ⟩-open)
        → pb-projₛ U V f W ∈ ⟨ c ⟩-reg (mk-open-set (pb-open Hf HW)) (mk-open-set HW)

    coerce-reg
      : ∀ {U} {m} {V : ℙ (ℝ ^ m)} {f} → {p q : V ∈ ⟨ c ⟩-open}
      → f ∈ ⟨ c ⟩-reg U (mk-open-set p) → f ∈ ⟨ c ⟩-reg U (mk-open-set q)
    coerce-reg {c} = subst (λ p → ∣ ⟨ c ⟩-reg _ (mk-open-set p) _ ∣) prop!

    ×ₛ-≃ : (U V : ⟨ c ⟩-open-set) → (∣ U ∣ₛ × ∣ V ∣ₛ) ≃ ∣ ×-open-set U V ∣ₛ
    ×ₛ-≃ U V .fst = to-×ₛ U V
    ×ₛ-≃ U V .snd = is-iso→is-equiv $ iso (from-×ₛ U V)
      (λ x → Σ-prop-path! (Equiv.η (vec-sum-prod (U .dim)) (x .fst)))
      (λ x → Σ-prop-path! (ap fst (Equiv.ε (vec-sum-prod (U .dim)) _))
          ,ₚ Σ-prop-path! (ap snd (Equiv.ε (vec-sum-prod (U .dim)) _)))

    ⟨_∣_⟩-reg
      : (c c' : Reg) (U : ⟨ c ⟩-open-set) (V : ⟨ c' ⟩-open-set) → ℙ (∣ U ∣ₛ → ∣ V ∣ₛ)
    ⟨ c ∣ d ⟩-reg U V f .∣_∣ =
      (Σ[ H≤ ∈ c ≤ d ] f ∈ ⟨ c ⟩-reg U (⊆-open-set H≤ V)) ∗ (f ∈ is-const)
    ⟨ c ∣ d ⟩-reg U V f .is-tr = hlevel 1

    id-reg' : ∀ {U} → (λ x → x) ∈ ⟨ c ∣ c ⟩-reg U U
    id-reg' = inl (≤-refl , coerce-reg id-reg)

    const-reg' : ∀ {U V} (x : ∣ V ∣ₛ) → (λ _ → x) ∈ ⟨ c ∣ c' ⟩-reg U V
    const-reg' x = inr (inc (x , refl))

    ∘-reg'
      : ∀ {c d e U V W f g}
      → f ∈ ⟨ d ∣ e ⟩-reg V W → g ∈ ⟨ c ∣ d ⟩-reg U V → f ∘ g ∈ ⟨ c ∣ e ⟩-reg U W
    ∘-reg' {c} {f = f} {g} Hf Hg = case Hf of λ where
      (inl (H≤ , Hf')) → case Hg of λ where
        (inl (H≤' , Hg')) →
          inl (≤-trans H≤' H≤ , coerce-reg (∘-reg (⊆-reg H≤' _ Hf') Hg'))
        (inr Hconst) → case Hconst of λ x Hx p → inr (inc (f (x , Hx) , ap (f ∘_) p))
      (inr Hconst) → case Hconst of λ x Hx p → inr (inc ((x , Hx) , ap (_∘ g) p))
