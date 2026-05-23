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

    ⟨_⟩-open-set : Reg → Type
    ⟨ c ⟩-open-set = Σ[ m ∈ Nat ] ∫ₚ (⟨ c ⟩-open {m})

    mk-open-set : ∀ {m} {U : ℙ (ℝ ^ m)} → U ∈ ⟨ c ⟩-open → ⟨ c ⟩-open-set
    mk-open-set p = _ , _ , p

    ⊆-open-set : c ≤ c' → ⟨ c' ⟩-open-set → ⟨ c ⟩-open-set
    ⊆-open-set H≤ (_ , _ , U-open) = mk-open-set (⊆-open H≤ _ U-open)

    ℝ-open-set : ∀ m → ⟨ c ⟩-open-set
    ℝ-open-set m = mk-open-set (⊤-open m)

    ∣_∣ₛ : ⟨ c ⟩-open-set → Type
    ∣ m , U , _ ∣ₛ = ∫ₚ U

    ×-open-set : ⟨ c ⟩-open-set → ⟨ c ⟩-open-set → ⟨ c ⟩-open-set
    ×-open-set (_ , _ , U-open) (_ , _ , V-open) = mk-open-set (×-open U-open V-open)

    to-×ₛ : (U V : ⟨ c ⟩-open-set) → ∣ U ∣ₛ × ∣ V ∣ₛ → ∣ ×-open-set U V ∣ₛ
    to-×ₛ (m , U , _) (n , V , _) (x , y) =
      x .fst ++ y .fst
      , subst (_∈ U) (sym $ ap fst (Equiv.ε (vec-sum-prod m) _)) (x .snd)
      , subst (_∈ V) (sym $ ap snd (Equiv.ε (vec-sum-prod m) _)) (y .snd)

    from-×ₛ : (U V : ⟨ c ⟩-open-set) → ∣ ×-open-set U V ∣ₛ → ∣ U ∣ₛ × ∣ V ∣ₛ
    from-×ₛ U V (xy , p , q) = let x , y = split {m = U .fst} xy in (x , p) , (y , q)

    field
      ⟨_⟩-reg : (c : Reg) (U V : ⟨ c ⟩-open-set) → ℙ (∣ U ∣ₛ → ∣ V ∣ₛ)
      ⊆-reg
        : ∀ {U V} (H≤ : c ≤ c')
        → ⟨ c' ⟩-reg U V ⊆ ⟨ c ⟩-reg (⊆-open-set H≤ U) (⊆-open-set H≤ V)

      id-reg    : ∀ {U} → (λ x → x) ∈ ⟨ c ⟩-reg U U
      const-reg : ∀ {U V} (x : ∣ V ∣ₛ) → (λ _ → x) ∈ ⟨ c ⟩-reg U V
      ∘-reg
        : ∀ {U V W f g}
        → f ∈ ⟨ c ⟩-reg V W → g ∈ ⟨ c ⟩-reg U V → f ∘ g ∈ ⟨ c ⟩-reg U W

      tup-reg
        : ∀ {U V W f g}
        → f ∈ ⟨ c ⟩-reg U V → g ∈ ⟨ c ⟩-reg U W
        → to-×ₛ V W ∘ ⟨ f , g ⟩ ∈ ⟨ c ⟩-reg U (×-open-set V W)
      proj-reg₁ : ∀ {U V} → fst ∘ from-×ₛ U V ∈ ⟨ c ⟩-reg (×-open-set U V) U
      proj-reg₂ : ∀ {U V} → snd ∘ from-×ₛ U V ∈ ⟨ c ⟩-reg (×-open-set U V) V

    coerce-reg
      : ∀ {U} {m} {V : ℙ (ℝ ^ m)} {f} → {p q : V ∈ ⟨ c ⟩-open}
      → f ∈ ⟨ c ⟩-reg U (mk-open-set p) → f ∈ ⟨ c ⟩-reg U (mk-open-set q)
    coerce-reg {c} = subst (λ p → ∣ ⟨ c ⟩-reg _ (mk-open-set p) _ ∣) prop!

    ×ₛ-≃ : (U V : ⟨ c ⟩-open-set) → (∣ U ∣ₛ × ∣ V ∣ₛ) ≃ ∣ ×-open-set U V ∣ₛ
    ×ₛ-≃ U V .fst = to-×ₛ U V
    ×ₛ-≃ U V .snd = is-iso→is-equiv $ iso (from-×ₛ U V)
      (λ x → Σ-prop-path! (Equiv.η (vec-sum-prod (U .fst)) (x .fst)))
      (λ x → Σ-prop-path! (ap fst (Equiv.ε (vec-sum-prod (U .fst)) _))
          ,ₚ Σ-prop-path! (ap snd (Equiv.ε (vec-sum-prod (U .fst)) _)))

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
